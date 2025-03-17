extern crate proc_macro;
use proc_macro::TokenStream;
use quote::quote;
use syn::parse::{Parse, ParseStream};
use syn::{DeriveInput, Expr, Ident, Lit, LitInt, LitStr, Token};

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
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // name
        let name_ident: Ident = input.parse()?;
        if name_ident != "name" {
            return Err(syn::Error::new(name_ident.span(), "expected 'name'"));
        }
        input.parse::<Token![=]>()?;
        let name = input.parse::<LitStr>()?.value();

        input.parse::<Token![,]>()?;

        // stack_args
        let stack_args_ident: Ident = input.parse()?;
        if stack_args_ident != "stack_args" {
            return Err(syn::Error::new(
                stack_args_ident.span(),
                "expected 'stack_args'",
            ));
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
                return Err(syn::Error::new(
                    ident.span(),
                    "expected stack_args to be either an integer or N",
                ));
            }
        } else {
            return Err(syn::Error::new(
                input.span(),
                "expected stack_args to be either an integer or N",
            ));
        };

        input.parse::<Token![,]>()?;

        // immediates
        let immediates_ident: Ident = input.parse()?;
        if immediates_ident != "immediates" {
            return Err(syn::Error::new(
                immediates_ident.span(),
                "expected 'immediates'",
            ));
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
            return Err(syn::Error::new(returns_ident.span(), "expected 'returns'"));
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
