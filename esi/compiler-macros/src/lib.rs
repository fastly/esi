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
    name: LitStr,
    stack_args: LitInt,
    immediates: LitInt,
    returns: LitInt,
}
impl Parse for MetaAttr {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // name
        let name_ident: Ident = input.parse()?;
        if name_ident != "name" {
            return Err(syn::Error::new(name_ident.span(), "expected 'name'"));
        }
        input.parse::<Token![=]>()?;
        let name: LitStr = input.parse()?;

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
        let stack_args: LitInt = input.parse()?;

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
        let immediates: LitInt = input.parse()?;

        input.parse::<Token![,]>()?;

        // returns
        let returns_ident: Ident = input.parse()?;
        if returns_ident != "returns" {
            return Err(syn::Error::new(returns_ident.span(), "expected 'returns'"));
        }
        input.parse::<Token![=]>()?;
        let returns: LitInt = input.parse()?;

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

            let mut name_value = None;
            let mut stack_args_value = None;
            let mut immediates_value = None;
            let mut returns_value = None;

            // Look for the #[meta(...)] attribute.
            for attr in &variant.attrs {
                if attr.path().is_ident("meta") {
                    let meta_attr: MetaAttr =
                        attr.parse_args().expect("Failed to parse meta attribute");
                    name_value = Some(meta_attr.name.value());
                    stack_args_value = Some(
                        meta_attr
                            .stack_args
                            .base10_parse::<usize>()
                            .expect("Failed to parse stack_args"),
                    );
                    immediates_value = Some(
                        meta_attr
                            .immediates
                            .base10_parse::<usize>()
                            .expect("Failed to parse immediates"),
                    );
                    returns_value = Some(
                        meta_attr
                            .returns
                            .base10_parse::<usize>()
                            .expect("Failed to parse returns"),
                    );
                }
            }

            // Ensure all values were provided.

            let name_value = name_value.unwrap_or_else(|| {
                panic!(
                    "Variant {} is missing the #[meta(name = ...)] attribute",
                    variant_ident
                )
            });
            variant_names.push(quote! {
                #name::#variant_ident => #name_value,
            });

            let stack_args_value = stack_args_value.unwrap_or_else(|| {
                panic!(
                    "Variant {} is missing the #[meta(stack_args = ...)] attribute",
                    variant_ident
                )
            });
            variant_stack_args.push(quote! {
                #name::#variant_ident => #stack_args_value,
            });

            let immediates_value = immediates_value.unwrap_or_else(|| {
                panic!(
                    "Variant {} is missing the immediates value in the attribute",
                    variant_ident
                )
            });

            variant_immediates.push(quote! {
                #name::#variant_ident => #immediates_value,
            });

            let returns_value = returns_value.unwrap_or_else(|| {
                panic!(
                    "Variant {} is missing the returns value in the attribute",
                    variant_ident
                )
            });

            variant_returns.push(quote! {
                #name::#variant_ident => #returns_value,
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
