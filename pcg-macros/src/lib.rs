use proc_macro::TokenStream;
use quote::{ToTokens, quote};
use syn::{Data, DeriveInput, Fields, GenericParam, Type, parse_macro_input};

/// Derive macro for `DisplayWithCtxt` on enums where each variant has a single field.
///
/// This generates an implementation that requires a context type `Ctxt` where
/// `Ctxt: Copy` and each variant's inner type implements `DisplayWithCtxt<Ctxt>`.
///
/// Example:
/// ```ignore
/// #[derive(DisplayWithCtxt)]
/// pub enum FunctionCallOrLoop<FunctionCallData, LoopData> {
///     FunctionCall(FunctionCallData),
///     Loop(LoopData),
/// }
/// ```
///
/// Generates:
/// ```ignore
/// impl<FunctionCallData, LoopData, Ctxt: Copy> DisplayWithCtxt<Ctxt>
///     for FunctionCallOrLoop<FunctionCallData, LoopData>
/// where
///     FunctionCallData: DisplayWithCtxt<Ctxt>,
///     LoopData: DisplayWithCtxt<Ctxt>,
/// {
///     fn display_output(&self, ctxt: Ctxt, mode: OutputMode) -> DisplayOutput {
///         match self {
///             FunctionCallOrLoop::FunctionCall(inner) => inner.display_output(ctxt, mode),
///             FunctionCallOrLoop::Loop(inner) => inner.display_output(ctxt, mode),
///         }
///     }
/// }
/// ```
#[proc_macro_derive(DisplayWithCtxt)]
pub fn derive_display_with_ctxt(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = &input.ident;
    let generics = &input.generics;

    let Data::Enum(data_enum) = &input.data else {
        return syn::Error::new_spanned(&input, "DisplayWithCtxt can only be derived for enums")
            .to_compile_error()
            .into();
    };

    let mut variant_arms = Vec::new();
    let mut field_types: Vec<&Type> = Vec::new();

    for variant in &data_enum.variants {
        let variant_name = &variant.ident;

        match &variant.fields {
            Fields::Unnamed(fields) if fields.unnamed.len() == 1 => {
                let field = fields.unnamed.first().unwrap();
                field_types.push(&field.ty);
                variant_arms.push(quote! {
                    #name::#variant_name(inner) => inner.display_output(ctxt, mode)
                });
            }
            _ => {
                return syn::Error::new_spanned(
                    variant,
                    "DisplayWithCtxt requires each variant to have exactly one unnamed field",
                )
                .to_compile_error()
                .into();
            }
        }
    }

    let (_impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let existing_where_predicates = where_clause.map(|w| &w.predicates);

    let where_bounds = field_types.iter().map(|ty| {
        quote! { #ty: crate::utils::display::DisplayWithCtxt<Ctxt> }
    });

    let existing_impl_params: Vec<_> = generics
        .params
        .iter()
        .map(|param| {
            match param {
                GenericParam::Type(ty) => {
                    let ident = &ty.ident;
                    let bounds = &ty.bounds;
                    if bounds.is_empty() {
                        quote! { #ident }
                    } else {
                        quote! { #ident: #bounds }
                    }
                }
                other => other.to_token_stream(),
            }
        })
        .collect();

    let expanded = quote! {
        impl<#(#existing_impl_params,)* Ctxt: Copy> crate::utils::display::DisplayWithCtxt<Ctxt>
            for #name #ty_generics
        where
            #(#where_bounds,)*
            #existing_where_predicates
        {
            fn display_output(
                &self,
                ctxt: Ctxt,
                mode: crate::utils::display::OutputMode,
            ) -> crate::utils::display::DisplayOutput {
                match self {
                    #(#variant_arms,)*
                }
            }
        }
    };

    TokenStream::from(expanded)
}
