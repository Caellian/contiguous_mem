use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use syn::{punctuated::Punctuated, spanned::Spanned, *};

use crate::path::{PathMatch, SegmentMatch};

use super::StrongType;

#[derive(Clone)]
pub struct FutureType<'a> {
    pub output: StrongType<'a>,
    pub source_span: Option<Span>,
}

impl<'a> FutureType<'a> {
    pub fn to_type(&self) -> Result<Type> {
        self.output.to_type().map(|ty| {
            Type::ImplTrait(TypeImplTrait {
                impl_token: token::Impl::default(),
                bounds: Punctuated::from_iter(std::iter::once(TypeParamBound::Trait(TraitBound {
                    paren_token: None,
                    modifier: TraitBoundModifier::None,
                    lifetimes: None,
                    path: Path {
                        leading_colon: None,
                        segments: Punctuated::from_iter([
                            PathSegment::from(Ident::new("core", Span::call_site())),
                            PathSegment::from(Ident::new("future", Span::call_site())),
                            PathSegment {
                                ident: Ident::new("Future", Span::call_site()),
                                arguments: PathArguments::AngleBracketed(
                                    AngleBracketedGenericArguments {
                                        colon2_token: None,
                                        lt_token: token::Lt::default(),
                                        args: Punctuated::from_iter(std::iter::once(
                                            GenericArgument::AssocType(AssocType {
                                                ident: Ident::new("Option", Span::call_site()),
                                                generics: None,
                                                eq_token: token::Eq::default(),
                                                ty,
                                            }),
                                        )),
                                        gt_token: token::Gt::default(),
                                    },
                                ),
                            },
                        ]),
                    },
                }))),
            })
        })
    }

    pub fn span(&self) -> Span {
        self.source_span.unwrap_or_else(Span::call_site)
    }
}

impl PartialEq for FutureType<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.output == other.output
    }
}

static FUTURE_MATCH: PathMatch<'static> = PathMatch {
    segments: &[
        SegmentMatch::OneOf(&["std", "core"]),
        SegmentMatch::Exact("future"),
        SegmentMatch::Exact("Future"),
    ],
    required_length: 1,
};

impl<'a> TryFrom<&'a TraitBound> for FutureType<'a> {
    type Error = Error;

    fn try_from(bound: &'a TraitBound) -> Result<Self> {
        if bound.path.segments.is_empty() || !FUTURE_MATCH.check(&bound.path) {
            return Err(Error::new_spanned(bound, "unexpected Future path"));
        }

        let args = &bound.path.segments.last().unwrap().arguments;

        let generic_args = match args {
            PathArguments::AngleBracketed(it) => &it.args,
            _ => {
                return Err(Error::new_spanned(
                    args,
                    "expected an angle bracketed generic argument",
                ))
            }
        };

        if generic_args.len() != 1 {
            return Err(Error::new_spanned(
                args,
                "expected a single generic argument",
            ));
        }

        match &generic_args[0] {
            GenericArgument::AssocType(it) if it.ident == "Output" && it.generics.is_none() => {
                Ok(FutureType {
                    output: StrongType::from(&it.ty),
                    source_span: Some(bound.span()),
                })
            }
            _ => Err(Error::new_spanned(
                args,
                "expected generic argument to be an 'Output' associated trait type",
            )),
        }
    }
}

impl<'a> TryFrom<&'a Type> for FutureType<'a> {
    type Error = Error;

    fn try_from(ty: &'a Type) -> Result<Self> {
        let bounds = match ty {
            Type::ImplTrait(TypeImplTrait { bounds, .. })
            | Type::TraitObject(TypeTraitObject { bounds, .. }) => bounds,
            _ => {
                return Err(Error::new_spanned(
                    ty,
                    "expected Future dyn trait or impl trait",
                ))
            }
        };

        bounds
            .iter()
            .find_map(|bound| match bound {
                TypeParamBound::Trait(trait_bound) => FutureType::try_from(trait_bound).ok(),
                _ => None,
            })
            .ok_or(Error::new_spanned(bounds, "expected a Future trait bound"))
    }
}

impl<'a> ToTokens for FutureType<'a> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(self.to_type().unwrap().to_token_stream())
    }
}
