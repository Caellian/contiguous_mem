use proc_macro2::{Ident, Span};
use quote::{quote, ToTokens};
use syn::{
    parse::Parse,
    parse_quote,
    punctuated::Punctuated,
    spanned::Spanned,
    token::{self},
    visit_mut::VisitMut,
    Attribute, Error, GenericParam, Generics, ImplItem, ImplItemFn, ItemImpl, Path, PathArguments,
    Result, ReturnType, Signature, TraitBound, Type,
};
use typestry::{ResultType, StrongType};

use crate::{
    traversal::*,
    util::{Destructure, TokenEq},
};

const IMPL_DETAILS: &str = "ImplDetails";

pub struct MemoryImpl {
    pub original: ItemImpl,
    pub attrs: Vec<Attribute>,
    pub generics: Generics,
    pub self_ty: Path,
    pub brace_token: token::Brace,
    pub items: Vec<ImplItem>,
}

impl Parse for MemoryImpl {
    fn parse(input: syn::parse::ParseStream) -> Result<Self> {
        let original = input.parse::<ItemImpl>()?;
        let ItemImpl {
            attrs,
            mut generics,
            trait_,
            self_ty: source_ty,
            brace_token,
            mut items,
            ..
        } = original.clone();

        if let Some(t) = trait_ {
            return Err(Error::new_spanned(
                t.1,
                "gen_sync doesn't work for trait implementations",
            ));
        }
        drop(trait_);

        let error_map: Vec<(Type, Type)> = vec![
            (
                syn::parse_str("MemoryError").unwrap(),
                syn::parse_str("crate::error::SyncMemoryError").unwrap(),
            ),
            (
                syn::parse_str("RegionBorrowError").unwrap(),
                syn::parse_str("crate::error::LockingError").unwrap(),
            ),
        ];

        let impl_name = proc_generics(&mut generics)?;
        let self_ty = proc_self_name(source_ty, &impl_name)?;

        let initial_types: Vec<(Ident, StrongType)> = items
            .iter()
            .filter_map(|it| match it {
                ImplItem::Fn(fun) => Some((
                    fun.sig.ident.clone(),
                    StrongType::from(Into::<Type>::into(Destructure(&fun.sig.output))),
                )),
                _ => None,
            })
            .collect();

        let mut sync_methods = Vec::new();
        let mut last_changed_sigs = 0;

        if let Some(impl_name) = &impl_name {
            for item in &mut items {
                specialize_impl_generic(item, impl_name);
            }
        }

        loop {
            let mut errors = Vec::new();

            let first_pass = sync_methods.len() == 0;
            for item in &mut items {
                match proc_impl_item(item, &sync_methods, &initial_types, &error_map, first_pass) {
                    Ok(changed) if changed => {
                        if let ImplItem::Fn(fun) = item {
                            sync_methods.push(fun.sig.clone())
                        }
                    }
                    Err(err) => {
                        errors.push(err);
                    }
                    _ => {}
                }
            }

            if !errors.is_empty() {
                let mut sum = errors.remove(0);
                errors.into_iter().for_each(|it| sum.combine(it));
                return Err(sum);
            }

            if sync_methods.len() != last_changed_sigs {
                last_changed_sigs = sync_methods.len();
            } else {
                break;
            }
        }

        Ok(Self {
            original,
            attrs,
            generics,
            self_ty,
            brace_token,
            items,
        })
    }
}

impl ToTokens for MemoryImpl {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let original = &self.original;
        let generics = &self.generics;
        let self_ty = &self.self_ty;
        let items = &self.items;
        tokens.extend(quote! {
            #original

            impl #generics #self_ty {
                #(#items)*
            }
        });
    }
}

static SYNCABLE_TRAITS: &[&str] = &["ReadableInner", "WritableInner"];

fn specialize_impl_generic(item: &mut ImplItem, impl_name: &(Ident, TraitBound)) {
    match item {
        ImplItem::Const(_) | ImplItem::Fn(_) | ImplItem::Type(_) => {
            SpecializeGenericArg::new(impl_name.0.clone(), "ImplConcurrent")
                .with_qualifier(Qualifier::new(
                    impl_name.1.clone(),
                    &[
                        "StateRef",
                        "SharedRef",
                        "Base",
                        "Tracker",
                        "PushResult",
                        "GROW",
                    ],
                ))
                .visit_impl_item_mut(item);
        }
        _ => {}
    }
}

fn proc_impl_item(
    item: &mut ImplItem,
    sync_methods: &[Signature],
    initial_types: &[(Ident, StrongType)],
    error_map: &[(Type, Type)],
    first_pass: bool,
) -> Result<bool> {
    let mut sig_changed = false;
    if let ImplItem::Fn(fun) = item {
        let lock_err = syn::parse_str("crate::error::LockingError")?;
        sig_changed = match first_pass {
            true => MapUnwrappedInvocation::within_impl_fn(SYNCABLE_TRAITS, fun),
            false => {
                TrySelf::within_impl_fn(sync_methods, initial_types, &lock_err, fun)?
                    && !sync_methods.iter().any(|it| it.ident == fun.sig.ident)
            }
        };

        if sig_changed {
            apply_return_transform(fun)?;

            let mut s = ResultMapping::new(error_map, lock_err);
            s.visit_return_type_mut(&mut fun.sig.output);
            if let Some(err) = s.error() {
                return Err(err);
            }
        }
    }
    Ok(sig_changed)
}

fn apply_return_transform(fun: &mut ImplItemFn) -> Result<()> {
    match &fun.sig.output {
        ReturnType::Default => return Ok(()),
        ReturnType::Type(_, ty) => match ResultType::try_from(ty.as_ref()) {
            Err(_) => return Ok(()),
            Ok(_) => {
                // continue if returning a result
            }
        },
    };

    // FIXME: Double wraps in Ok even return was initially a Result.
    for expr in FindReturns::within_impl_fn(fun)?.into_iter() {
        *expr = parse_quote!(Ok(#expr));
    }

    Ok(())
}

trait FilterOutExt<T> {
    fn filter_out(&mut self, filter: impl Fn(&T) -> bool) -> Vec<T>;
}
impl<T: Clone, P: Default> FilterOutExt<T> for Punctuated<T, P> {
    fn filter_out(&mut self, filter: impl Fn(&T) -> bool) -> Vec<T> {
        let mut result = Vec::with_capacity(self.len());

        let items: Vec<T> = self.iter().map(Clone::clone).collect();
        self.clear();
        for item in items {
            if filter(&item) {
                result.push(item);
            } else {
                self.push(item);
            }
        }

        result
    }
}

fn is_impl_param(param: &GenericParam) -> bool {
    if let GenericParam::Type(ty) = param {
        for bound in ty.bounds.iter() {
            if let syn::TypeParamBound::Trait(trait_) = bound {
                let is_details = trait_
                    .path
                    .segments
                    .last()
                    .map(|s| s.ident.to_string() == IMPL_DETAILS)
                    .unwrap_or_default();

                if is_details {
                    return true;
                }
            }
        }
    }

    false
}

fn proc_generics(generics: &mut Generics) -> Result<Option<(Ident, TraitBound)>> {
    let mut ty = match generics.params.filter_out(is_impl_param).into_iter().next() {
        Some(GenericParam::Type(it)) => it,
        _ => return Ok(None),
    };

    let bound = match ty.bounds.pop().map(|it| it.into_value()) {
        Some(syn::TypeParamBound::Trait(it)) if ty.bounds.is_empty() => it,
        _ => {
            return Err(Error::new(
                ty.bounds.span(),
                "expected a single trait bound for implementation param",
            ));
        }
    };

    Ok(Some((ty.ident, bound)))
}

fn proc_self_name(self_name: Box<Type>, impl_name: &Option<(Ident, TraitBound)>) -> Result<Path> {
    match *self_name {
        Type::Path(tp) => {
            let path_span = tp.span();
            let mut result = tp.path;

            let last_segment = result
                .segments
                .last_mut()
                .ok_or(Error::new(path_span, "empty type path"))?;

            // remove impl_name if defined
            if let Some(impl_name) = impl_name {
                if let PathArguments::AngleBracketed(generic_args) = &mut last_segment.arguments {
                    generic_args.args.filter_out(|it| {
                        if let syn::GenericArgument::Type(Type::Path(path)) = it {
                            path.path
                                .segments
                                .first()
                                .map(|it| it.ident == impl_name.0)
                                .unwrap_or_default()
                        } else {
                            false
                        }
                    });
                }
            }

            // prefix ident with Sync
            last_segment.ident = Ident::new(
                format!("Sync{}", last_segment.ident.to_string()).as_str(),
                Span::call_site(),
            );

            Ok(result)
        }
        other => Err(Error::new_spanned(
            other,
            "expected a default implementation struct",
        )),
    }
}
