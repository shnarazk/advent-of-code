use {
    proc_macro::TokenStream,
    quote::{quote, ToTokens},
    syn::{parse::*, parse_macro_input, ImplItem, ItemImpl},
};

struct Args {
    items: Vec<syn::ExprLit>,
}

impl Parse for Args {
    fn parse(input: ParseStream) -> Result<Self> {
        let items =
            syn::punctuated::Punctuated::<syn::ExprLit, syn::Token![,]>::parse_terminated(input)
                .expect("error");
        Ok(Args {
            items: items.into_iter().collect(),
        })
    }
}

/// Set year, day, and output types as `usize` on `AdventOfCode` implementaion
// ### Example
/// ```
/// #[aoc_at(2021, 25)]
/// impl AdventOfCode for Puzzle { ... }
/// ```
#[proc_macro_attribute]
pub fn aoc_at(attrs: TokenStream, input: TokenStream) -> TokenStream {
    let vars = parse_macro_input!(attrs as Args);
    let year = &vars.items[0];
    let day = &vars.items[1];
    let assign_year = TokenStream::from(quote! { const YEAR: usize =#year; });
    let assign_day = TokenStream::from(quote! { const DAY: usize =#day; });
    let output_type1 = TokenStream::from(quote! { type Output1 = usize; });
    let output_type2 = TokenStream::from(quote! { type Output2 = usize; });
    let mut implementation: ItemImpl = syn::parse(input).expect("only be applied to impl");
    implementation
        .items
        .push(syn::parse::<ImplItem>(assign_year).expect(""));
    implementation
        .items
        .push(syn::parse::<ImplItem>(assign_day).expect(""));
    implementation
        .items
        .push(syn::parse::<ImplItem>(output_type1).expect(""));
    implementation
        .items
        .push(syn::parse::<ImplItem>(output_type2).expect(""));
    TokenStream::from(implementation.to_token_stream())
}
