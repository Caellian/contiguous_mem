use proc_macro2::Span;
use syn::{punctuated::Punctuated, spanned::Spanned, *};

use crate::path::{PathMatch, SegmentMatch};

use super::StrongType;

#[derive(Clone)]
pub struct ResultType<'a> {
    pub ok_ty: StrongType<'a>,
    pub err_ty: StrongType<'a>,
    pub source_span: Option<Span>,
}

impl<'a> ResultType<'a> {
    pub fn new(ok_ty: StrongType<'a>, err_ty: StrongType<'a>) -> Self {
        ResultType {
            ok_ty,
            err_ty,
            source_span: None,
        }
    }

    pub fn merge(&self, other: &ResultType<'a>) -> ResultType<'a> {
        let ok_ty = match self.ok_ty.is_some() {
            true => &self.ok_ty,
            false => &other.ok_ty,
        }
        .clone();

        let err_ty = match self.err_ty.is_some() {
            true => &self.err_ty,
            false => &other.err_ty,
        }
        .clone();

        ResultType {
            ok_ty,
            err_ty,
            source_span: self.source_span.or(other.source_span),
        }
    }

    pub fn with_ok(self, ok: impl Into<StrongType<'a>>) -> ResultType<'a> {
        ResultType {
            ok_ty: ok.into(),
            ..self
        }
    }

    pub fn with_err(self, err: impl Into<StrongType<'a>>) -> ResultType<'a> {
        ResultType {
            err_ty: err.into(),
            ..self
        }
    }

    pub fn to_type(&self) -> Result<Type> {
        match (self.ok_ty.to_type(), self.err_ty.to_type()) {
            (Ok(ok), Ok(err)) => Ok(result_type(ok, err)),
            (Ok(_), Err(err)) => {
                let mut result = Error::new(self.span(), "can't infer Err type");
                result.extend([err]);
                Err(result)
            }
            (Err(err), Ok(_)) => {
                let mut result = Error::new(self.span(), "can't infer Ok type");
                result.extend([err]);
                Err(result)
            }
            (Err(ok_err), Err(err_err)) => {
                let mut result = Error::new(self.span(), "can't infer Ok, nor Err types");
                result.extend([ok_err, err_err]);
                Err(result)
            }
        }
    }

    pub fn span(&self) -> Span {
        self.source_span.unwrap_or_else(Span::call_site)
    }
}

impl Default for ResultType<'_> {
    fn default() -> Self {
        ResultType::new(StrongType::default(), StrongType::default())
    }
}

impl PartialEq for ResultType<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.ok_ty == other.ok_ty && self.err_ty == other.err_ty
    }
}

static RESULT_MATCH: PathMatch<'static> = PathMatch {
    segments: &[
        SegmentMatch::OneOf(&["std", "core"]),
        SegmentMatch::Exact("result"),
        SegmentMatch::Exact("Result"),
    ],
    required_length: 1,
};
static OK_MATCH: PathMatch<'static> = PathMatch {
    segments: &[
        SegmentMatch::OneOf(&["std", "core"]),
        SegmentMatch::Exact("result"),
        SegmentMatch::Optional("Result"),
        SegmentMatch::Exact("Ok"),
    ],
    required_length: 1,
};
static ERR_MATCH: PathMatch<'static> = PathMatch {
    segments: &[
        SegmentMatch::OneOf(&["std", "core"]),
        SegmentMatch::Exact("result"),
        SegmentMatch::Optional("Result"),
        SegmentMatch::Exact("Err"),
    ],
    required_length: 1,
};

impl<'a> TryFrom<&'a Type> for ResultType<'a> {
    type Error = Error;

    fn try_from(ty: &'a Type) -> std::result::Result<Self, Self::Error> {
        #[inline]
        fn arg_ty<'a>(generic: &'a GenericArgument) -> StrongType<'a> {
            match generic {
                GenericArgument::Type(it) => StrongType::from(it),
                other => StrongType::Unknown {
                    location: other.span(),
                    reason: "expected a type generic argument",
                },
            }
        }

        let path = match ty {
            Type::Path(it) if it.qself.is_none() => &it.path,
            _ => return Err(Error::new(ty.span(), "expected a Result type path")),
        };

        if path.segments.is_empty() || !RESULT_MATCH.check(&path) {
            return Err(Error::new_spanned(path, "unexpected Result path"));
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

        if generic_args.len() != 2 {
            return Err(Error::new_spanned(args, "expected two generic arguments"));
        }

        let ok_ty = arg_ty(&generic_args[0]);
        let err_ty = arg_ty(&generic_args[1]);

        Ok(ResultType {
            ok_ty,
            err_ty,
            source_span: Some(ty.span()),
        })
    }
}

pub fn result_type(ok: Type, err: Type) -> Type {
    Type::Path(TypePath {
        qself: None,
        path: Path {
            leading_colon: None,
            segments: Punctuated::from_iter([
                PathSegment::from(Ident::new("core", Span::call_site())),
                PathSegment::from(Ident::new("result", Span::call_site())),
                PathSegment {
                    ident: Ident::new("Result", Span::call_site()),
                    arguments: PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                        colon2_token: None,
                        lt_token: token::Lt::default(),
                        args: Punctuated::from_iter([
                            GenericArgument::Type(ok),
                            GenericArgument::Type(err),
                        ]),
                        gt_token: token::Gt::default(),
                    }),
                },
            ]),
        },
    })
}

impl<'a> From<ResultPattern<'a>> for ResultType<'a> {
    fn from(value: ResultPattern<'a>) -> Self {
        match value {
            ResultPattern::Ok(ok) => ResultType {
                ok_ty: StrongType::from(ok),
                err_ty: StrongType::Unknown {
                    location: ok.span(),
                    reason: "can't infer Err type from Ok result pattern",
                },
                source_span: Some(ok.span()),
            },
            ResultPattern::Err(err) => ResultType {
                ok_ty: StrongType::Unknown {
                    location: err.span(),
                    reason: "can't infer Ok type from Err result pattern",
                },
                err_ty: StrongType::from(err),
                source_span: Some(err.span()),
            },
        }
    }
}

impl<'a> TryFrom<&'a Pat> for ResultType<'a> {
    type Error = ();

    fn try_from(value: &'a Pat) -> std::result::Result<Self, Self::Error> {
        match ResultPattern::of_pattern(value) {
            Some(it) => Ok(ResultType::from(it)),
            None => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a ExprMatch> for ResultType<'a> {
    type Error = Option<Error>;

    fn try_from(value: &'a ExprMatch) -> std::result::Result<Self, Self::Error> {
        let mut result = ResultType::default();
        for arm in &value.arms {
            if result.ok_ty.is_some() && result.err_ty.is_some() {
                break;
            }

            if let Ok(it) = ResultType::try_from(&arm.pat) {
                result = result.merge(&it);
            }
        }

        Ok(result)
    }
}

pub(crate) fn is_ok_path(path: &Path) -> bool {
    OK_MATCH.check(path)
}

pub(crate) fn is_err_path(path: &Path) -> bool {
    ERR_MATCH.check(path)
}

pub enum ResultPattern<'a> {
    Ok(&'a Pat),
    Err(&'a Pat),
}

impl<'a> ResultPattern<'a> {
    pub fn check(pat: &'a Pat) -> bool {
        let tuple_struct = match pat {
            Pat::TupleStruct(it) => it,
            _ => return false,
        };

        if tuple_struct.path.segments.is_empty() || tuple_struct.elems.len() != 1 {
            return false;
        }

        is_ok_path(&tuple_struct.path) || is_err_path(&tuple_struct.path)
    }

    pub fn of_pattern(pat: &'a Pat) -> Option<Self> {
        let tuple_struct = match pat {
            Pat::TupleStruct(it) => it,
            _ => return None,
        };

        if tuple_struct.path.segments.is_empty() || tuple_struct.elems.len() != 1 {
            return None;
        }

        if is_ok_path(&tuple_struct.path) {
            return Some(ResultPattern::Ok(&tuple_struct.elems[0]));
        }

        if is_err_path(&tuple_struct.path) {
            return Some(ResultPattern::Err(&tuple_struct.elems[0]));
        }

        None
    }

    pub fn ok(&self) -> Option<&'a Pat> {
        match self {
            ResultPattern::Ok(it) => Some(it),
            ResultPattern::Err(_) => None,
        }
    }

    pub fn err(&self) -> Option<&'a Pat> {
        match self {
            ResultPattern::Ok(_) => None,
            ResultPattern::Err(it) => Some(it),
        }
    }

    #[inline]
    pub fn is_ok(&self) -> bool {
        matches!(self, ResultPattern::Ok(_))
    }

    #[inline]
    pub fn is_err(&self) -> bool {
        matches!(self, ResultPattern::Ok(_))
    }

    #[inline]
    pub fn unwrap(&self) -> &'a Pat {
        match self {
            ResultPattern::Ok(it) | ResultPattern::Err(it) => it,
        }
    }
}
