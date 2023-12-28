use {
    proc_macro::TokenStream,
    quote::{quote, ToTokens},
    std::str::FromStr,
    syn::{parse::*, parse_macro_input, ImplItem, ItemImpl},
};
mod color;

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
/// #[aoc(2021, 25)]
/// impl AdventOfCode for Puzzle { ... }
/// ```
#[proc_macro_attribute]
pub fn aoc(attrs: TokenStream, input: TokenStream) -> TokenStream {
    let vars = parse_macro_input!(attrs as Args);
    let year = &vars.items[0];
    let day = &vars.items[1];
    let assign_year = TokenStream::from(quote! { const YEAR: usize = #year; });
    let assign_day = TokenStream::from(quote! { const DAY: usize = #day; });
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

/// Set year, day on `AdventOfCode` implementaion
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
    let assign_year = TokenStream::from(quote! { const YEAR: usize = #year; });
    let assign_day = TokenStream::from(quote! { const DAY: usize = #day; });
    let mut implementation: ItemImpl = syn::parse(input).expect("only be applied to impl");
    implementation
        .items
        .push(syn::parse::<ImplItem>(assign_year).expect(""));
    implementation
        .items
        .push(syn::parse::<ImplItem>(assign_day).expect(""));
    TokenStream::from(implementation.to_token_stream())
}

// #[aco_arms(2021, 25)]
// #[aco_arms(2021)]
#[proc_macro]
pub fn aoc_arms(attrs: TokenStream) -> TokenStream {
    fn to_usize(token: &syn::ExprLit) -> usize {
        if let syn::Lit::Int(ref lit_int) = token.lit {
            if let Ok(n) = lit_int.base10_parse::<usize>() {
                return n;
            }
        }
        panic!();
    }
    let vars = parse_macro_input!(attrs as Args);
    let year: usize = to_usize(&vars.items[0]);
    let day_from: usize = 1;
    let day_to: usize = vars.items.get(1).map_or(25, to_usize);
    let match_body: String = format!(
        "match day {{ {} _=> panic!(\"{}an invalid day{}\"), }}\n",
        (day_from..=day_to)
            .map(|d| {
                format!(
                "{} => {{ if config.serialize {{y{:0>4}::day{:0>2}::Puzzle::solve(config, desc, part);}} else {{ println!(\"{}{{}}{}\", y{:0>4}::day{:0>2}::Puzzle::solve(config, desc, part));}} }}",
                d,
                year, d,
                color::BLUE,
                color::RESET,
                year, d,
            )})
            .collect::<Vec<String>>()
            .join("\n"),
        color::RED,
        color::RESET,
    );
    TokenStream::from_str(&match_body).unwrap()
}
