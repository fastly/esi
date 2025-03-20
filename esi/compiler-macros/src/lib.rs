extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::{
    parse_macro_input, DeriveInput, Error, Expr, Ident, Lit, LitBool, LitInt, LitStr, Result, Token,
};

//use syn::{Data, DataStruct, Fields};

#[proc_macro_derive(Constraints, attributes(meta))]
pub fn instructions(input: TokenStream) -> TokenStream {
    let ast = syn::parse_macro_input!(input as syn::DeriveInput);
    impl_meta(&ast)
}

// Define a helper type to parse the contents of #[meta(name = "opname", stack_args = 0, immediates = 0, returns = 0)]
struct MetaAttr {
    name: String,
    stack_args: usize,
    immediates: usize,
    returns: usize,
}
impl Parse for MetaAttr {
    fn parse(input: ParseStream) -> Result<Self> {
        // name
        let name_ident: Ident = input.parse()?;
        if name_ident != "name" {
            return Err(Error::new(name_ident.span(), "expected 'name'"));
        }
        input.parse::<Token![=]>()?;
        let name = input.parse::<LitStr>()?.value();

        input.parse::<Token![,]>()?;

        // stack_args
        let stack_args_ident: Ident = input.parse()?;
        if stack_args_ident != "stack_args" {
            return Err(Error::new(stack_args_ident.span(), "expected 'stack_args'"));
        }
        input.parse::<Token![=]>()?;

        let stack_args: usize = if input.peek(LitInt) {
            input
                .parse::<LitInt>()?
                .base10_parse::<usize>()
                .expect("Failed to parse stack_args")
        } else if input.peek(Ident) {
            let ident: Ident = input.parse()?;
            if ident == "N" {
                usize::MAX
            } else {
                return Err(Error::new(
                    ident.span(),
                    "expected stack_args to be either an integer or N",
                ));
            }
        } else {
            return Err(Error::new(
                input.span(),
                "expected stack_args to be either an integer or N",
            ));
        };

        input.parse::<Token![,]>()?;

        // immediates
        let immediates_ident: Ident = input.parse()?;
        if immediates_ident != "immediates" {
            return Err(Error::new(immediates_ident.span(), "expected 'immediates'"));
        }
        input.parse::<Token![=]>()?;
        let immediates: usize = input
            .parse::<LitInt>()?
            .base10_parse::<usize>()
            .expect("Failed to parse immediates");

        input.parse::<Token![,]>()?;

        // returns
        let returns_ident: Ident = input.parse()?;
        if returns_ident != "returns" {
            return Err(Error::new(returns_ident.span(), "expected 'returns'"));
        }
        input.parse::<Token![=]>()?;
        let returns: usize = input
            .parse::<LitInt>()?
            .base10_parse::<usize>()
            .expect("Failed to parse returns");

        Ok(MetaAttr {
            name,
            stack_args,
            immediates,
            returns,
        })
    }
}
fn impl_meta(ast: &DeriveInput) -> TokenStream {
    let name = &ast.ident;
    let mut variant_names = Vec::new();
    let mut variant_stack_args = Vec::new();
    let mut variant_immediates = Vec::new();
    let mut variant_returns = Vec::new();
    let mut variant_consts = Vec::new();

    if let syn::Data::Enum(data_enum) = &ast.data {
        for variant in data_enum.variants.iter() {
            let variant_ident = &variant.ident;
            let variant_discriminant = match variant
                .discriminant
                .clone()
                .expect("Failed to find a discriminant")
            {
                (_, Expr::Lit(discrim)) => match discrim.lit {
                    Lit::Int(discrim_int) => discrim_int
                        .base10_parse::<u8>()
                        .expect("Failed to parse u8 from discriminant"),
                    _ => panic!("Discriminant is not integer"),
                },
                _ => panic!("Failed to get literal discriminant"),
            };

            let const_variant = Ident::new(
                &("OP_".to_owned() + &variant_ident.to_string().to_uppercase()),
                variant_ident.span(),
            );
            variant_consts.push(quote! {
                pub const #const_variant: u8 = #variant_discriminant;
            });

            let mut meta_attr: Option<MetaAttr> = None;

            // Look for the #[meta(...)] attribute.
            for attr in &variant.attrs {
                if attr.path().is_ident("meta") {
                    meta_attr = Some(attr.parse_args().expect("Failed to parse meta attribute"));
                }
            }

            let meta_attr = meta_attr.unwrap_or_else(|| panic!("Failed to find meta attributes"));

            let name_value = meta_attr.name;
            variant_names.push(quote! {
                #name::#variant_ident => #name_value,
            });

            let stack_args = meta_attr.stack_args;
            variant_stack_args.push(quote! {
                #name::#variant_ident => #stack_args,
            });

            let immediates = meta_attr.immediates;
            variant_immediates.push(quote! {
                #name::#variant_ident => #immediates,
            });

            let returns = meta_attr.returns;
            variant_returns.push(quote! {
                #name::#variant_ident => #returns,
            });
        }
    } else {
        panic!("#[derive(Constraints)] can only be applied to enums");
    }

    let gen = quote! {
        #(#variant_consts)*
        impl #name {
            pub fn name(&self) -> &'static str {
                match self {
                    #(#variant_names)*
                }
            }

            pub fn expected_stack_args(&self) -> usize {
                match self {
                    #(#variant_stack_args)*
                }
            }
            pub fn expected_immediates(&self) -> usize {
                match self {
                    #(#variant_immediates)*
                }
            }
            pub fn returns(&self) -> usize {
                match self {
                    #(#variant_returns)*
                }
            }
        }
    };

    gen.into()
}

// ABI Function Macro

/// Holds the parameters for `#[abi_fn(args=0, has_return=true)]`.
struct AbiFnArgs {
    args_int: Option<usize>, // e.g. 0  (either this field, or the range field should be None)
    has_return: Option<bool>, // e.g. true
}

impl Parse for AbiFnArgs {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut args_int = None;
        let mut has_return = None;

        // Parse zero or more `key = value` pairs, separated by commas.
        // Example: `range = "0..=0", has_return = true`
        while !input.is_empty() {
            let key: Ident = input.parse()?; // e.g. `range` or `has_return`
            input.parse::<Token![=]>()?; // consume '='

            match key.to_string().as_str() {
                "args" => {
                    args_int = if input.peek(LitInt) {
                        Some(
                            input
                                .parse::<LitInt>()?
                                .base10_parse::<usize>()
                                .expect("Failed to parse args"),
                        )
                    } else if input.peek(Ident) {
                        let ident: Ident = input.parse()?;
                        if ident == "N" {
                            Some(usize::MAX)
                        } else {
                            return Err(Error::new(
                                ident.span(),
                                "expected args to be either an integer or N",
                            ));
                        }
                    } else {
                        return Err(Error::new(
                            input.span(),
                            "expected args to be either an integer or N",
                        ));
                    };
                }
                "has_return" => {
                    // e.g. true or false
                    let lit: LitBool = input.parse()?;
                    has_return = Some(lit.value());
                }
                other => {
                    // Produce a raw parse error if unknown keys appear.
                    return Err(syn::Error::new(
                        key.span(),
                        format!("Unrecognized #[abi_fn] parameter: {other}"),
                    ));
                }
            }

            // Optional comma before next pair, if any
            if !input.is_empty() {
                input.parse::<Token![,]>()?;
            }
        }

        Ok(AbiFnArgs {
            args_int,
            has_return,
        })
    }
}

/// Attribute macro that generates both:
/// - a normal Rust function (the user's code),
/// - and a `pub const {fn_name}: BuiltinFn = ...;` referencing that function.
///
/// # Example
///
/// ```ignore
/// #[abi_fn(args = 0, has_return = true)]
/// pub fn ping(args: usize, state: &mut ExecutionState) {
///     // ...
/// }
/// ```
#[proc_macro_attribute]
pub fn abi_fn(attr: TokenStream, item: TokenStream) -> TokenStream {
    // 1. Parse the attribute arguments into our `AbiFnArgs`
    let args = parse_macro_input!(attr as AbiFnArgs);

    // Must have `args`, or we emit a compile_error! block
    let args_str = match args.args_int {
        Some(s) => {
            if s == usize::MAX {
                "Args::Variadic".to_string()
            } else {
                format!("Args::Constant({args})", args = s)
            }
        }
        None => {
            return r#"
                compile_error!("Missing `args` in #[abi_fn(range=N, has_return=...)]");
            "#
            .parse()
            .unwrap();
        }
    };

    // If `has_return` wasn't specified, default it to false
    let has_return = args.has_return.unwrap_or(false);

    // 2. Convert the user's function code into a string for naive scanning
    let item_str = item.to_string();

    // 3. Find the function name by searching for "fn " and reading until a non-identifier char.
    let func_name = match naive_find_fn_name(&item_str) {
        Some(name) => name,
        None => {
            return r#"
                compile_error!("Could not locate function name. Make sure your code has a normal `fn name(...)`.");
            "#
            .parse()
            .unwrap();
        }
    };

    // 4. Generate the final code by simply concatenating:
    //    - The original user function
    //    - A `pub const <fn_name>` referencing that function
    //
    //    Adjust `::my_crate::BuiltinFn` etc. to your real crate paths.
    let expanded = format!(
        r#"
{original}

#[allow(non_upper_case_globals)]
pub const {fn_name}_builtin: BuiltinFn = BuiltinFn {{
    func: {fn_name},
    sig: FnSignature {{
        args: {args_str},
        has_return: {has_return_bool},
    }},
}};
"#,
        original = item_str,
        fn_name = func_name,
        args_str = args_str,
        has_return_bool = has_return,
    );

    // Convert our new source code string back into a TokenStream
    expanded.parse().unwrap_or_else(|err| {
        // In extremely rare cases if you produce invalid code,
        // you can surface that as a compile error:
        format!(r#"compile_error!("macro generated invalid code: {err}");"#)
            .parse()
            .unwrap()
    })
}

/// Very naive "fn name" scanner:
/// - Finds the first occurrence of "fn "
/// - Reads subsequent alphanumeric/_ characters as the name
fn naive_find_fn_name(source: &str) -> Option<String> {
    let idx = source.find("fn ")?;
    // skip "fn " => 3 chars
    let after_fn = &source[idx + 3..];

    let mut name = String::new();
    for c in after_fn.chars() {
        if c.is_alphanumeric() || c == '_' {
            name.push(c);
        } else {
            break;
        }
    }

    if name.is_empty() {
        None
    } else {
        Some(name)
    }
}
