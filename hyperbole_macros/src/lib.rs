//! Procedural macros for hyperbole.
//!
//! The macros exported here are documented in [hyperbole].
#![warn(rust_2018_idioms)]
use proc_macro::TokenStream;
use quote::quote;
use syn::{
    parse_macro_input,
    punctuated::Punctuated,
    token::{Await, Comma, Dot},
    Error, FnArg, ItemFn, Pat, PatType,
};

#[proc_macro_attribute]
pub fn record_args(_: TokenStream, item: TokenStream) -> TokenStream {
    let fn_item = parse_macro_input!(item as ItemFn);

    // extract the basic stuff
    let fn_async = fn_item.sig.asyncness;
    let fn_generics = &fn_item.sig.generics;
    let fn_name = &fn_item.sig.ident;
    let fn_ret_ty = &fn_item.sig.output;

    // tracks whether arg[i] is a named field
    let mut arg_is_field = vec![false; fn_item.sig.inputs.len()];

    // translate fn_item's args into named fields if necessary
    let fn_args_ty: Punctuated<_, Comma> = (fn_item.sig.inputs.iter())
        .enumerate()
        .map(|(i, arg)| match arg {
            FnArg::Typed(PatType { pat, ty, .. }) => match &**pat {
                Pat::Ident(ident) => match format!("{}", ident.ident) {
                    id if !id.starts_with('_') => {
                        arg_is_field[i] = true;
                        quote!(::hyperbole::f![#ident : #ty])
                    }
                    _ => quote!(#ty),
                },
                pat => Error::new_spanned(pat, "#[record_args] arguments must be identifiers")
                    .to_compile_error(),
            },
            arg => Error::new_spanned(arg, "`self` parameter can't be translated into an hlist")
                .to_compile_error(),
        })
        .collect();

    // compute accessors for each element of the hlist
    let fn_args_call: Punctuated<_, Comma> = (arg_is_field.into_iter())
        .enumerate()
        .map(|(depth, is_field)| {
            // 0th arg: cx.head[.into_inner()]
            // 1st arg: cx.tail.head[.into_inner()]
            // ... etc
            let mut acc: Punctuated<_, Dot> = Punctuated::new();

            // take the name of the outer argument hlist
            acc.push(quote!(__cx_hyperbole_record_args_arg));
            // offset 'depth' into it
            acc.extend((0..depth).map(|_| quote!(tail)));
            // and grab the head
            acc.push(quote!(head));

            // if arg is a named field, we call into_inner() to get the contained value
            if is_field {
                acc.push(quote!(into_inner()));
            }

            acc
        })
        .collect();

    // make sure to call .await if we're dealing with an async fn
    let fn_dot = fn_async.map(|_| Dot::default());
    let fn_await = fn_async.map(|_| Await::default());

    let output = quote!(
        #fn_async fn #fn_name#fn_generics(
            __cx_hyperbole_record_args_arg: ::hyperbole::Hlist![#fn_args_ty],
        ) #fn_ret_ty {
            #fn_item

            #fn_name(#fn_args_call) #fn_dot #fn_await
        }
    );

    output.into()
}
