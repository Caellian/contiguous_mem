use impl_block::MemoryImpl;
use quote::ToTokens;
use syn::parse_macro_input;

mod impl_block;
mod traversal;
mod util;

#[proc_macro_attribute]
pub fn gen_sync(
    _attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let model: MemoryImpl = parse_macro_input!(input as MemoryImpl);
    model.into_token_stream().into()
}
