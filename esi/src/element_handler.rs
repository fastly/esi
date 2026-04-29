//! Shared element processing trait used by both streaming (`Processor`) and
//! expression-evaluation (`call_user_function`) contexts.
//!
//! # Design
//!
//! Both processing contexts handle the same set of ESI tags but differ in
//! exactly four behaviours:
//!
//! | Hook            | Streaming (`DocumentHandler`)         | Function (`FunctionHandler`)               |
//! |-----------------|----------------------------------------|--------------------------------------------|
//! | `on_return`     | ignore (no return concept at top level)| evaluate & signal `Flow::Return(val)`      |
//! | `on_include`    | dispatch & enqueue the fragment        | error – not allowed in function bodies     |
//! | `on_eval`       | fetch, parse, re-process               | error – not allowed in function bodies     |
//! | `on_try`        | build parallel-fetch queues            | ignore (no dispatcher available)           |
//! | `on_function`   | register in context                    | error – nested definitions not supported   |
//!
//! Everything else – `Text`/`Html`/`Expr` output, `Assign`, `Vars`, `Choose`,
//! `Foreach`, `Break` – is implemented once as default methods on this trait.

use bytes::Bytes;

use crate::{
    error::ESIError,
    expression::{eval_expr, EvalContext, Value},
    parser_types::{Element, Expr, IncludeAttributes, Tag, WhenBranch},
    Result,
};

/// Unified control-flow signal returned by every element-processing step.
pub enum Flow {
    /// Keep going with the next element.
    Continue,
    /// Exit the nearest enclosing `esi:foreach` loop.
    Break,
    /// Return from the enclosing user-defined function with the given value.
    Return(Value),
}

/// Trait that abstracts over both ESI processing contexts.
///
/// Implementors provide context-specific behaviour through the required hooks;
/// all shared tag-handling logic lives in the default method implementations.
pub trait ElementHandler {
    // -------------------------------------------------------------------------
    // Required: context access
    // -------------------------------------------------------------------------

    /// Mutable access to the evaluation context (variables, request metadata, …).
    fn ctx(&mut self) -> &mut EvalContext;

    /// Write bytes to the context-appropriate output
    /// (directly to a `Write` for streaming, or to a `Vec<u8>` for functions).
    fn write_bytes(&mut self, bytes: Bytes) -> Result<()>;

    // -------------------------------------------------------------------------
    // Required: context-specific hooks
    // -------------------------------------------------------------------------

    /// Handle `<esi:return value="…"/>`.
    /// Streaming: ignore (returns `Flow::Continue`).
    /// Function: evaluate `value`, return `Flow::Return(val)`.
    fn on_return(&mut self, value: &Expr) -> Result<Flow>;

    /// Handle `<esi:include …/>`.
    /// Streaming: dispatch the fragment request and enqueue it.
    /// Function: return an error.
    fn on_include(&mut self, attrs: &IncludeAttributes) -> Result<Flow>;

    /// Handle `<esi:eval …/>`.
    /// Streaming: fetch the fragment, parse it as ESI, re-process in current context.
    /// Function: return an error.
    fn on_eval(&mut self, attrs: &IncludeAttributes) -> Result<Flow>;

    /// Handle `<esi:try>…</esi:try>`.
    /// Streaming: build parallel-dispatch queues for each attempt and the except clause.
    /// Function: ignore (returns `Flow::Continue`).
    fn on_try(
        &mut self,
        attempt_events: Vec<Vec<Element>>,
        except_events: Vec<Element>,
    ) -> Result<Flow>;

    /// Handle `<esi:function name="…">…</esi:function>`.
    /// Streaming: register in the evaluation context.
    /// Function: return an error (nested definitions are not supported).
    fn on_function(&mut self, name: String, body: Vec<Element>) -> Result<Flow>;

    /// Non-blocking check for completed fragment requests, flushing any ready output.
    ///
    /// Called after processing each top-level element in the main parse loop.
    /// Default is a no-op — only meaningful in the streaming context.
    fn process_queue(&mut self) -> Result<()> {
        Ok(())
    }

    // -------------------------------------------------------------------------
    // Default: shared dispatch
    // -------------------------------------------------------------------------

    /// Process a slice of elements, returning early on non-`Continue` flow.
    fn process_elements(&mut self, elements: &[Element]) -> Result<Flow> {
        for elem in elements {
            let flow = self.process(elem)?;
            if !matches!(flow, Flow::Continue) {
                return Ok(flow);
            }
        }
        Ok(Flow::Continue)
    }

    /// Dispatch a single element to the appropriate handler.
    ///
    /// All context-neutral tags call shared default helpers; context-specific
    /// tags call the required hooks above.
    fn process(&mut self, element: &Element) -> Result<Flow> {
        match element {
            Element::Content(text) | Element::Html(text) => {
                self.write_bytes(text.clone())?;
                Ok(Flow::Continue)
            }

            Element::Expr(expr) => {
                let val = eval_expr(expr, self.ctx()).map_err(|e| {
                    ESIError::ExpressionError(format!("{e}, in expression: {expr}"))
                })?;
                if !matches!(val, Value::Null) {
                    let bytes = val.to_bytes();
                    if !bytes.is_empty() {
                        self.write_bytes(bytes)?;
                    }
                }
                Ok(Flow::Continue)
            }

            Element::Esi(Tag::Assign {
                name,
                subscript,
                value,
            }) => self.handle_assign(name, subscript.as_ref(), value),

            Element::Esi(Tag::Vars { name }) => self.handle_vars(name.as_deref()),

            Element::Esi(Tag::Include { attrs }) => self.on_include(attrs),

            Element::Esi(Tag::Eval { attrs }) => self.on_eval(attrs),

            Element::Esi(Tag::Choose {
                when_branches,
                otherwise_events,
            }) => self.handle_choose(when_branches, otherwise_events),

            Element::Esi(Tag::Foreach {
                collection,
                item,
                content,
            }) => self.handle_foreach(collection, item.as_deref(), content),

            Element::Esi(Tag::Break) => Ok(Flow::Break),

            Element::Esi(Tag::Try {
                attempt_events,
                except_events,
            }) => self.on_try(attempt_events.clone(), except_events.clone()),

            Element::Esi(Tag::Function { name, body }) => {
                self.on_function(name.clone(), body.clone())
            }

            Element::Esi(Tag::Return { value }) => self.on_return(value),

            // Other standalone tags (e.g. Otherwise, When, Attempt, Except at
            // top level) are parser artefacts that should never appear here.
            Element::Esi(_) => Ok(Flow::Continue),
        }
    }

    // -------------------------------------------------------------------------
    // Default: shared tag handlers
    // -------------------------------------------------------------------------

    /// Handle `<esi:assign name="…" [value="…"]/>` — shared between both contexts.
    fn handle_assign(
        &mut self,
        name: &str,
        subscript: Option<&Expr>,
        value: &Expr,
    ) -> Result<Flow> {
        // Propagate the error if evaluation fails
        let val = eval_expr(value, self.ctx()).map_err(|e| {
            ESIError::ExpressionError(format!("{e}, in assignment '{name}' = {value}"))
        })?;

        // If there's a subscript, this is an assignment to an existing collection item
        if let Some(subscript_expr) = subscript {
            // Subscript assignment: modify existing collection
            if let Ok(subscript_val) = eval_expr(subscript_expr, self.ctx()) {
                let key_str = subscript_val.to_string();
                self.ctx().set_variable(name, Some(&key_str), val)?;
            }
        } else {
            // Regular assignment
            self.ctx().set_variable(name, None, val)?;
        }
        Ok(Flow::Continue)
    }

    /// Handle `<esi:vars name="…"/>` — sets the match-capture variable name.
    fn handle_vars(&mut self, name: Option<&str>) -> Result<Flow> {
        if let Some(n) = name {
            self.ctx().set_match_name(n);
        }
        Ok(Flow::Continue)
    }

    /// Handle `<esi:choose>…</esi:choose>` — evaluate when-branches in order,
    /// fall through to otherwise if none match.
    fn handle_choose(
        &mut self,
        when_branches: &[WhenBranch],
        otherwise_events: &[Element],
    ) -> Result<Flow> {
        let mut chose_branch = false;

        for when_branch in when_branches {
            if let Some(ref match_name) = when_branch.match_name {
                self.ctx().set_match_name(match_name);
            }

            match eval_expr(&when_branch.test, self.ctx()) {
                Ok(test_result) if test_result.to_bool() => {
                    let flow = self.process_elements(&when_branch.content)?;
                    if !matches!(flow, Flow::Continue) {
                        return Ok(flow);
                    }
                    chose_branch = true;
                    break;
                }
                _ => continue,
            }
        }

        // No when matched - process otherwise
        if !chose_branch {
            return self.process_elements(otherwise_events);
        }

        Ok(Flow::Continue)
    }

    /// Handle `<esi:foreach collection="…" [item="…"]>…</esi:foreach>`.
    fn handle_foreach(
        &mut self,
        collection: &Expr,
        item: Option<&str>,
        content: &[Element],
    ) -> Result<Flow> {
        // Evaluate the collection expression
        let collection_value = eval_expr(collection, self.ctx()).unwrap_or(Value::Null);

        // Convert to a list if needed (snapshot items to release any borrow)
        let items = match &collection_value {
            Value::List(items) => items.borrow().clone(),
            Value::Dict(map) => map
                .borrow()
                .iter()
                .map(|(k, v)| {
                    // Convert dict entries to a list of 2-element lists [key, value]
                    Value::new_list(vec![Value::Text(k.clone().into()), v.clone()])
                })
                .collect(),
            Value::Null => Vec::new(),
            other => vec![other.clone()], // Treat single values as a list of one
        };

        // Default item variable name if not specified
        let item_var = item.unwrap_or("item").to_string();

        // Iterate through items
        for item_value in items {
            // Set the item variable
            self.ctx().set_variable(&item_var, None, item_value)?;

            // Process content for this iteration
            match self.process_elements(content)? {
                Flow::Continue => {}
                Flow::Break => break,
                ret @ Flow::Return(_) => return Ok(ret),
            }
        }

        Ok(Flow::Continue)
    }
}
