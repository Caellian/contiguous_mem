use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use syn::{punctuated::Punctuated, spanned::Spanned, *};

use crate::path::{PathMatch, SegmentMatch};

use super::StrongType;

#[derive(Clone)]
pub struct OptionType<'a> {
    pub some_ty: StrongType<'a>,
    pub source_span: Option<Span>,
}

impl<'a> OptionType<'a> {
    pub fn to_type(&self) -> Result<Type> {
        self.some_ty.to_type().map(|ty| {
            Type::Path(TypePath {
                qself: None,
                path: Path {
                    leading_colon: None,
                    segments: Punctuated::from_iter([
                        PathSegment::from(Ident::new("core", Span::call_site())),
                        PathSegment::from(Ident::new("option", Span::call_site())),
                        PathSegment {
                            ident: Ident::new("Option", Span::call_site()),
                            arguments: PathArguments::AngleBracketed(
                                AngleBracketedGenericArguments {
                                    colon2_token: None,
                                    lt_token: token::Lt::default(),
                                    args: Punctuated::from_iter(std::iter::once(
                                        GenericArgument::Type(ty),
                                    )),
                                    gt_token: token::Gt::default(),
                                },
                            ),
                        },
                    ]),
                },
            })
        })
    }

    pub fn span(&self) -> Span {
        self.source_span.unwrap_or_else(Span::call_site)
    }
}

impl PartialEq for OptionType<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.some_ty == other.some_ty
    }
}

impl<'a> ToTokens for OptionType<'a> {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(self.to_type().unwrap().to_token_stream())
    }
}

static OPTION_MATCH: PathMatch<'static> = PathMatch {
    segments: &[
        SegmentMatch::OneOf(&["std", "core"]),
        SegmentMatch::Exact("option"),
        SegmentMatch::Exact("Option"),
    ],
    required_length: 1,
};
static SOME_MATCH: PathMatch<'static> = PathMatch {
    segments: &[
        SegmentMatch::OneOf(&["std", "core"]),
        SegmentMatch::Exact("option"),
        SegmentMatch::Optional("Option"),
        SegmentMatch::Exact("Some"),
    ],
    required_length: 1,
};
static NONE_MATCH: PathMatch<'static> = PathMatch {
    segments: &[
        SegmentMatch::OneOf(&["std", "core"]),
        SegmentMatch::Exact("option"),
        SegmentMatch::Optional("Option"),
        SegmentMatch::Exact("None"),
    ],
    required_length: 1,
};

impl<'a> TryFrom<&'a Type> for OptionType<'a> {
    type Error = Error;

    fn try_from(ty: &'a Type) -> Result<Self> {
        let path = match ty {
            Type::Path(type_path) if type_path.qself.is_none() => &type_path.path,
            _ => return Err(Error::new_spanned(ty, "expected an Option type path")),
        };

        if path.segments.is_empty() || !OPTION_MATCH.check(&path) {
            return Err(Error::new_spanned(path, "unexpected Option path"));
        }

        let args = &path.segments.last().unwrap().arguments;

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
            GenericArgument::Type(it) => Ok(OptionType {
                some_ty: StrongType::from(it),
                source_span: Some(ty.span()),
            }),
            _ => Err(Error::new_spanned(
                args,
                "expected generic argument to be a type",
            )),
        }
    }
}

pub enum OptionPattern<'a> {
    Some(&'a Pat),
    None,
}

pub(crate) fn is_some_path(path: &Path) -> bool {
    SOME_MATCH.check(path)
}

pub(crate) fn is_none_path(path: &Path) -> bool {
    NONE_MATCH.check(path)
}

impl<'a> OptionPattern<'a> {
    pub fn check(pat: &'a Pat) -> bool {
        match pat {
            Pat::TupleStruct(tuple_struct) => {
                if tuple_struct.path.segments.is_empty() || tuple_struct.elems.len() != 1 {
                    return false;
                }

                is_some_path(&tuple_struct.path)
            }
            Pat::Path(ExprPath {
                path, qself: None, ..
            }) => {
                if path.segments.is_empty() {
                    return false;
                }

                is_none_path(&path)
            }
            _ => false,
        }
    }

    pub fn of_pattern(pat: &'a Pat) -> Option<Self> {
        match pat {
            Pat::TupleStruct(tuple_struct) => {
                if tuple_struct.path.segments.is_empty() || tuple_struct.elems.len() != 1 {
                    return None;
                }

                if is_some_path(&tuple_struct.path) {
                    return Some(OptionPattern::Some(&tuple_struct.elems[0]));
                }

                None
            }
            Pat::Path(ExprPath {
                path, qself: None, ..
            }) => {
                if path.segments.is_empty() {
                    return None;
                }

                if is_none_path(&path) {
                    return Some(OptionPattern::None);
                }

                None
            }
            _ => None,
        }
    }
}
