use std::fmt;
/// This struct is used to configure optional behaviour within the ESI processor.
///
/// ## Usage Example
/// ```rust,no_run
/// let config = esi::Configuration::default()
///     .with_namespace("app")
///     .with_recursion();
///
/// let processor = esi::Processor::new(config);
/// ```
#[derive(Clone)]
pub struct Configuration<'a> {
    /// The XML namespace to use when scanning for ESI tags. Defaults to `esi`.
    pub namespace: String,

    /// Whether or not to execute nested ESI tags within fetched fragments. Defaults to `false`.
    pub recursive: bool,

    /// Returns true if the esi:include with 'src' should be expanded, false to leave alone.
    pub is_match: &'a dyn Fn(&str) -> bool,
}

impl<'a> Default for Configuration<'a> {
    fn default() -> Self {
        Self {
            namespace: String::from("esi"),
            recursive: false,
            is_match: &|_| true,
        }
    }
}

impl<'a> fmt::Debug for Configuration<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Configuration")
            .field("namespace", &self.namespace)
            .field("recursive", &self.recursive)
            .finish()
    }
}

impl<'a> Configuration<'a> {
    /// Sets an alternative ESI namespace, which is used to identify ESI instructions.
    ///
    /// For example, setting this to `test` would cause the processor to only match tags like `<test:include>`.
    pub fn with_namespace(mut self, namespace: impl Into<String>) -> Self {
        self.namespace = namespace.into();
        self
    }

    /// Enables the processing of nested ESI tags within fetched fragments.
    pub fn with_recursion(mut self) -> Self {
        self.recursive = true;
        self
    }

    /// Sets a matcher to control what esi:includes are expanded, true to include, false to leave alone.
    pub fn with_matcher(mut self, matcher: &'a dyn Fn(&str) -> bool) -> Self {
        self.is_match = matcher;
        self
    }
}
