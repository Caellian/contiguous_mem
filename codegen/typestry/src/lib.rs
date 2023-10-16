use std::borrow::Cow;

use proc_macro2::Span;
use syn::{punctuated::Punctuated, spanned::Spanned, *};

mod util;
use util::*;

pub mod path;

mod loops;
pub use loops::*;

mod option;
pub use option::*;

mod result;
pub use result::*;

mod future;
pub use future::*;

mod consts;
use consts::const_type;

use crate::path::{variant_path_to_type, PathKind};

#[derive(Clone)]
#[non_exhaustive]
pub enum StrongType<'a> {
    Result(Box<ResultType<'a>>),
    Option(Box<OptionType<'a>>),
    Future(Box<FutureType<'a>>),
    Unit(Span),
    Other(Cow<'a, Type>),
    /// Returned when trying to infer the type from a pattern/expression which
    /// has no indications of the underlying type, such as `_`.
    Unknown {
        /// Token span which caused type inferrence to fail.
        location: Span,
        /// Explanation why type inferrence failed.
        reason: &'static str,
    },
}

impl<'a> StrongType<'a> {
    #[inline]
    pub fn is_some(&self) -> bool {
        if let StrongType::Unknown { .. } = self {
            false
        } else {
            true
        }
    }

    #[inline]
    pub fn some(self) -> Option<Self> {
        if let StrongType::Unknown { .. } = self {
            None
        } else {
            Some(self)
        }
    }

    pub fn to_type(&self) -> Result<Type> {
        match self {
            StrongType::Result(it) => it.to_type(),
            StrongType::Option(it) => it.to_type(),
            StrongType::Future(it) => it.to_type(),
            StrongType::Unit(_) => Ok(unit_type()),
            StrongType::Other(ty) => Ok((**ty).clone()),
            StrongType::Unknown { location, reason } => Err(Error::new(location.clone(), reason)),
        }
    }

    pub fn span(&self) -> Span {
        match self {
            StrongType::Result(res) => res.span(),
            StrongType::Option(opt) => opt.span(),
            StrongType::Future(fut) => fut.span(),
            StrongType::Other(it) => it.span(),
            StrongType::Unit(location) | StrongType::Unknown { location, .. } => location.clone(),
        }
    }

    pub fn map_value(self, f: impl FnOnce(StrongType) -> Self) -> Self {
        match self {
            StrongType::Unknown { .. } => self,
            other => f(other),
        }
    }

    pub fn map_reason(self, new_reason: &'static str) -> Self {
        match self {
            StrongType::Unknown { location, .. } => StrongType::Unknown {
                location,
                reason: new_reason,
            },
            other => other,
        }
    }

    #[inline]
    pub fn or(self, other: Self) -> Self {
        match self {
            StrongType::Unknown { .. } => other,
            known => known,
        }
    }

    #[inline]
    pub fn or_else(self, other: impl FnOnce() -> Self) -> Self {
        match self {
            StrongType::Unknown { .. } => other(),
            known => known,
        }
    }

    #[inline]
    pub fn and_then(self, f: impl FnOnce(StrongType) -> Self) -> Self {
        match self {
            StrongType::Unknown { .. } => self,
            known => f(known),
        }
    }

    pub fn index_result(&'a self) -> StrongType<'a> {
        match self {
            StrongType::Other(ty) => return index_result(ty.as_ref()),
            other => {
                return Self::Unknown {
                    location: other.span(),
                    reason: "can't infer type of indexed value that isn't a slice/array",
                }
            }
        };
    }
}

impl Default for StrongType<'_> {
    fn default() -> Self {
        StrongType::Unknown {
            location: Span::call_site(),
            reason: "default constructed type is unknown",
        }
    }
}

impl PartialEq for StrongType<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (StrongType::Result(self_), StrongType::Result(other)) => self_ == other,
            (StrongType::Option(self_), StrongType::Option(other)) => self_ == other,
            (StrongType::Future(self_), StrongType::Future(other)) => self_.output == other.output,
            (StrongType::Other(self_), StrongType::Other(other)) => self_.syntax_eq(other),
            (StrongType::Unit(a), StrongType::Unit(b))
            | (StrongType::Unknown { location: a, .. }, StrongType::Unknown { location: b, .. })
                if a.source_text().is_some() =>
            {
                a.source_text() == b.source_text()
            }
            _ => false,
        }
    }
}

impl<'a> From<&'a Type> for StrongType<'a> {
    #[inline]
    fn from(value: &'a Type) -> Self {
        StrongType::Other(Cow::Borrowed(value))
    }
}
impl<'a> From<Type> for StrongType<'a> {
    #[inline]
    fn from(value: Type) -> Self {
        StrongType::Other(Cow::Owned(value))
    }
}
impl<'a> From<Cow<'a, Type>> for StrongType<'a> {
    #[inline]
    fn from(value: Cow<'a, Type>) -> Self {
        StrongType::Other(value)
    }
}

fn index_result<'a>(ty: &'a Type) -> StrongType<'a> {
    match ty {
        Type::Array(it) => StrongType::from(it.elem.as_ref().clone()),
        Type::Group(it) => index_result(it.elem.as_ref()),
        Type::ImplTrait(TypeImplTrait { bounds, .. })
        | Type::TraitObject(TypeTraitObject { bounds, .. }) => bounds
            .iter()
            .find_map(|it| match it {
                TypeParamBound::Trait(it)
                    if it
                        .path
                        .segments
                        .last()
                        .map(|it| it.ident.to_string() == "Index")
                        .unwrap_or_default() =>
                {
                    let args = match &it.path.segments.last().unwrap().arguments {
                        PathArguments::AngleBracketed(it) => &it.args,
                        _ => return None,
                    };
                    if args.len() != 1 {
                        return None;
                    }
                    match &args[1] {
                        GenericArgument::Type(ty) => Some(StrongType::from(ty)),
                        _ => None,
                    }
                }
                _ => None,
            })
            .unwrap_or_else(|| StrongType::Unknown {
                location: ty.span(),
                reason: "can't infer type from trait",
            }),
        Type::Paren(it) => index_result(it.elem.as_ref()),
        Type::Reference(it) => {
            index_result(it.elem.as_ref()).map_value(|strong_ty| match strong_ty.to_type() {
                Ok(ty) => StrongType::from(Type::Reference(TypeReference {
                    and_token: token::And::default(),
                    lifetime: if let Some(life) = &it.lifetime {
                        Some(lifetime(life.ident.to_string()))
                    } else {
                        None
                    },
                    mutability: if it.mutability.is_some() {
                        Some(token::Mut::default())
                    } else {
                        None
                    },
                    elem: Box::new(ty),
                })),
                Err(err) => StrongType::Unknown {
                    location: err.span(),
                    reason: "can't infer inner reference type",
                },
            })
        }
        Type::Slice(it) => StrongType::from(it.elem.as_ref().clone()),
        other => StrongType::Unknown {
            location: other.span(),
            reason: "unable to infer index value type",
        },
    }
}

fn index_expr_elem<'a>(expr: &'a Expr) -> Option<Type> {
    match expr {
        Expr::Array(it) => it
            .elems
            .iter()
            .find_map(|e| StrongType::from(e).to_type().ok()),
        Expr::Repeat(it) => StrongType::from(it.expr.as_ref()).to_type().ok(),
        Expr::Block(ExprBlock { block, .. }) | Expr::Const(ExprConst { block, .. }) => {
            StrongType::from(block)
                .map_value(|ty| match ty {
                    StrongType::Other(other) => match index_result(&other) {
                        StrongType::Other(it) => StrongType::from(it.as_ref().clone()),
                        _ => StrongType::Unknown {
                            location: expr.span(),
                            reason: "can't infer block index value type",
                        },
                    },
                    _ => StrongType::Unknown {
                        location: expr.span(),
                        reason: "can't infer indexed value type",
                    },
                })
                .to_type()
                .ok()
        }
        _ => None,
    }
}

impl<'a> From<&'a ExprCall> for StrongType<'a> {
    fn from(call: &'a ExprCall) -> Self {
        if let Expr::Path(it) = call.func.as_ref() {
            if call.args.len() == 1 && !it.path.segments.is_empty() {
                let arg_ty = StrongType::from(&call.args[0]);
                if is_ok_path(&it.path) {
                    return StrongType::Result(Box::new(ResultType {
                        ok_ty: arg_ty,
                        err_ty: StrongType::Unknown {
                            location: call.span(),
                            reason: "can't infer Err type from Ok variant",
                        },
                        source_span: Some(call.span()),
                    }));
                }
                if is_err_path(&it.path) {
                    return StrongType::Result(Box::new(ResultType {
                        ok_ty: StrongType::Unknown {
                            location: call.span(),
                            reason: "can't infer Ok type from Err variant",
                        },
                        err_ty: arg_ty,
                        source_span: Some(call.span()),
                    }));
                }
                if is_some_path(&it.path) {
                    return StrongType::Option(Box::new(OptionType {
                        some_ty: arg_ty,
                        source_span: Some(call.span()),
                    }));
                }
            }
        }
        StrongType::Unknown {
            location: call.span(),
            reason: "can't infer expression call return type",
        }
    }
}

/*
impl<'a> From<&'a Path> for StrongType<'a> {
    fn from(path: &'a Path) -> Self {
         else {
            match PathKind::guess_for_path(path) {
                Some(PathKind::) => todo!(),
                None => todo!(),
            }
            if is_enum_path(path) {
                StrongType::Other(Cow::Owned(variant_path_to_type(path)))
            } else {
                StrongType::Other(Cow::Owned(Type::Path(TypePath {
                    qself: None,
                    path: path.clone(),
                })))
            }
        }
    }
}*/

impl<'a> From<&'a ExprPath> for StrongType<'a> {
    fn from(expr_path: &'a ExprPath) -> Self {
        const NOT_NONE: &str = "can't infer path type";

        if expr_path.qself.is_some() || expr_path.path.segments.is_empty() {
            return StrongType::Unknown {
                location: expr_path.span(),
                reason: NOT_NONE,
            };
        }

        if is_none_path(&expr_path.path) {
            return StrongType::Option(Box::new(OptionType {
                some_ty: StrongType::Unknown {
                    location: expr_path.span(),
                    reason: "can't infer Some type from None expression",
                },
                source_span: Some(expr_path.span()),
            }));
        } else {
            match PathKind::guess_for_path(&expr_path.path) {
                Some(PathKind::Const) if expr_path.path.segments.len() > 1 => {
                    return const_type(&expr_path.path)
                }
                // TODO: Soundness: path capitalization based type assumptions
                Some(PathKind::Variant) => {
                    return StrongType::from(variant_path_to_type(&expr_path.path));
                }
                Some(PathKind::Struct) => {
                    return StrongType::from(Type::Path(TypePath {
                        qself: expr_path.qself.clone(),
                        path: expr_path.path.clone(),
                    }))
                }
                _ => {}
            }
        }

        return StrongType::Unknown {
            location: expr_path.span(),
            reason: NOT_NONE,
        };
    }
}

impl<'a> From<&'a Expr> for StrongType<'a> {
    fn from(expr: &'a Expr) -> Self {
        match expr {
            Expr::Array(it) => {
                let elem = match it
                    .elems
                    .iter()
                    .find_map(|e| StrongType::from(e).to_type().ok())
                {
                    Some(it) => it,
                    None => {
                        return StrongType::Unknown {
                            location: it.span(),
                            reason: "can't infer element type",
                        };
                    }
                };

                StrongType::from(Type::Array(TypeArray {
                    bracket_token: token::Bracket::default(),
                    elem: Box::new(elem),
                    semi_token: token::Semi::default(),
                    len: Expr::Lit(ExprLit {
                        attrs: vec![],
                        lit: Lit::Int(LitInt::new(
                            it.elems.len().to_string().as_str(),
                            Span::call_site(),
                        )),
                    }),
                }))
            }
            Expr::Async(it) => StrongType::Future(Box::new(FutureType {
                output: StrongType::from(&it.block),
                source_span: Some(it.span()),
            })),
            Expr::Await(it) => match StrongType::from(it.base.as_ref()) {
                StrongType::Future(fut) => fut.output,
                _ => StrongType::Unknown {
                    location: it.span(),
                    reason: "can't infer result of awaiting expression",
                },
            },
            Expr::Binary(it) => {
                StrongType::from(it.left.as_ref()).or_else(|| StrongType::from(it.right.as_ref()))
            }
            Expr::Block(it) => StrongType::from(&it.block),
            Expr::Call(it) => StrongType::from(it),
            Expr::Path(it) => StrongType::from(it),
            Expr::Cast(it) => StrongType::from(it.ty.as_ref()),
            // TODO: Support closures
            Expr::Closure(_) => StrongType::Unknown {
                location: expr.span(),
                reason: "can't infer closure type",
            },
            Expr::Const(ExprConst { block, .. }) => StrongType::from(block),
            Expr::Group(it) => StrongType::from(it.expr.as_ref()),
            Expr::If(if_expr) => StrongType::from(&if_expr.then_branch).or_else(|| {
                if_expr
                    .else_branch
                    .as_ref()
                    .map(|(_, it)| StrongType::from(it.as_ref()))
                    .unwrap_or(StrongType::Unknown {
                        location: if_expr.span(),
                        reason: "can't infer type of if expression",
                    })
            }),
            Expr::Index(it) => match index_expr_elem(it.expr.as_ref()) {
                Some(it) => StrongType::from(it),
                _ => StrongType::Unknown {
                    location: it.span(),
                    reason: "can't infer element type",
                },
            },
            Expr::Lit(it) => StrongType::from(&it.lit),
            Expr::Match(match_expr) => match_expr
                .arms
                .iter()
                .find_map(|it| StrongType::from(it.body.as_ref()).some())
                .unwrap_or_else(|| StrongType::Unknown {
                    location: match_expr.span(),
                    reason: "can't infer type of match expression",
                }),
            Expr::Paren(it) => StrongType::from(it.expr.as_ref()),
            Expr::Range(it) => {
                let start = if let Some(start) = &it.start {
                    StrongType::from(start.as_ref())
                } else {
                    StrongType::default()
                };
                let ty = start.or_else(|| {
                    if let Some(end) = &it.end {
                        StrongType::from(end.as_ref())
                    } else {
                        StrongType::default()
                    }
                });

                let ty = match ty.to_type() {
                    Ok(it) => it,
                    Err(_) => {
                        return StrongType::Unknown {
                            location: it.span(),
                            reason: "can't infer range bound type",
                        }
                    }
                };

                let mut last_segment = match it.limits {
                    RangeLimits::HalfOpen(_) => {
                        PathSegment::from(Ident::new("Range", Span::call_site()))
                    }
                    RangeLimits::Closed(_) => {
                        PathSegment::from(Ident::new("RangeInclusive", Span::call_site()))
                    }
                };
                last_segment.arguments =
                    PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                        colon2_token: None,
                        lt_token: token::Lt::default(),
                        args: Punctuated::from_iter(std::iter::once(GenericArgument::Type(ty))),
                        gt_token: token::Gt::default(),
                    });

                StrongType::from(Type::Path(TypePath {
                    qself: None,
                    path: Path {
                        leading_colon: None,
                        segments: Punctuated::from_iter([
                            PathSegment::from(Ident::new("core", Span::call_site())),
                            PathSegment::from(Ident::new("range", Span::call_site())),
                            last_segment,
                        ]),
                    },
                }))
            }
            Expr::Reference(expr_ref) => StrongType::from(expr_ref.expr.as_ref())
                .to_type()
                .map(|ty| {
                    StrongType::from(Type::Reference(TypeReference {
                        and_token: token::And::default(),
                        lifetime: None,
                        mutability: expr_ref.mutability.clone(),
                        elem: Box::new(ty),
                    }))
                })
                .unwrap_or_else(|_| StrongType::Unknown {
                    location: expr_ref.span(),
                    reason: "can't infer reference type",
                }),
            Expr::Repeat(it) => {
                let elem = match StrongType::from(it.expr.as_ref()).to_type() {
                    Ok(it) => it,
                    Err(_) => {
                        return StrongType::Unknown {
                            location: it.span(),
                            reason: "can't infer element type",
                        };
                    }
                };

                StrongType::from(Type::Array(TypeArray {
                    bracket_token: token::Bracket::default(),
                    elem: Box::new(elem),
                    semi_token: token::Semi::default(),
                    len: it.len.as_ref().clone(),
                }))
            }
            Expr::Struct(it) => StrongType::from(Type::Path(TypePath {
                qself: None,
                path: it.path.clone(),
            })),
            Expr::Try(it) => match StrongType::from(it.expr.as_ref()) {
                StrongType::Result(result) => result.ok_ty,
                StrongType::Option(result) => result.some_ty,
                _ => StrongType::Unknown {
                    location: it.span(),
                    reason: "can't infer resulting type of try expression",
                },
            },
            Expr::TryBlock(it) => {
                let ok_ty = StrongType::from(&it.block);
                StrongType::Result(Box::new(ResultType {
                    ok_ty,
                    err_ty: StrongType::Unknown {
                        location: it.span(),
                        reason: "can't infer Err type from try block",
                    },
                    source_span: Some(it.span()),
                }))
            }
            Expr::Tuple(it) => {
                let types: Vec<_> = it
                    .elems
                    .iter()
                    .filter_map(|it| StrongType::from(it).to_type().ok())
                    .collect();

                // TODO: Support partial tuple inference
                if it.elems.len() != types.len() {
                    return StrongType::Unknown {
                        location: it.span(),
                        reason: "can't infer type of some tuple elements",
                    };
                }

                StrongType::from(Type::Tuple(TypeTuple {
                    paren_token: token::Paren::default(),
                    elems: Punctuated::from_iter(types.into_iter()),
                }))
            }
            Expr::Unary(op) => match op.op {
                UnOp::Deref(_) => StrongType::from(op.expr.as_ref())
                    .to_type()
                    .and_then(|ty| match ty {
                        Type::Reference(type_ref) => {
                            Ok(StrongType::from(type_ref.elem.as_ref().clone()))
                        }
                        _ => Err(Error::new_spanned(ty, "can't dereference type")),
                    })
                    .unwrap_or(StrongType::Unknown {
                        location: op.span(),
                        reason: "can't infer type of dereferenced expression",
                    }),
                UnOp::Not(_) => StrongType::from(ty_literal("bool")),
                UnOp::Neg(_) => StrongType::from(op.expr.as_ref()),
                _ => StrongType::Unknown {
                    location: op.span(),
                    reason: "can't infer type of unknown unary operation",
                },
            },
            Expr::Unsafe(ExprUnsafe { block, .. }) => StrongType::from(block),
            Expr::ForLoop(it) => StrongType::from(it),
            Expr::Loop(it) => StrongType::from(it),
            Expr::While(it) => StrongType::from(it),
            Expr::Field(_)
            | Expr::Infer(_)
            | Expr::MethodCall(_)
            | Expr::Macro(_)
            | Expr::Verbatim(_) => StrongType::Unknown {
                location: expr.span(),
                reason: "can't infer type from expression",
            },
            other => StrongType::Unit(other.span()),
        }
    }
}

pub static INT_TYPES: &[&str] = &[
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
];

impl<'a> From<&'a Lit> for StrongType<'a> {
    fn from(value: &'a Lit) -> Self {
        StrongType::from(match value {
            Lit::Str(_) => ref_ty_literal(Some(static_lifetime()), false, "str"),
            Lit::ByteStr(_) => ref_ty_literal(Some(static_lifetime()), false, "u8"),
            Lit::Byte(_) => ty_literal("u8"),
            Lit::Char(_) => ty_literal("char"),
            Lit::Int(it) => match it.suffix() {
                it if INT_TYPES.contains(&it) => ty_literal(it),
                _ => ty_literal("i32"),
            },
            Lit::Float(it) => match it.suffix() {
                "f64" => ty_literal("f64"),
                _ => ty_literal("f32"),
            },
            Lit::Bool(_) => ty_literal("bool"),
            other => {
                return StrongType::Unknown {
                    location: other.span(),
                    reason: "can't infer type of unknown literal",
                }
            }
        })
    }
}

impl<'a> From<&'a Pat> for StrongType<'a> {
    fn from(value: &'a Pat) -> Self {
        match value {
            Pat::Lit(literal) => StrongType::from(&literal.lit),
            Pat::Or(it) => it
                .cases
                .iter()
                .find_map(|it| StrongType::from(it).some())
                .unwrap_or_else(|| StrongType::Unknown {
                    location: it.span(),
                    reason: "can't infer type of any pattern cases",
                }),
            Pat::Paren(it) => StrongType::from(it.pat.as_ref()),
            Pat::Path(expr_path) => StrongType::from(expr_path),
            Pat::Range(range) => {
                if let Some(start) = &range.start {
                    if let Some(ty) = StrongType::from(start.as_ref()).some() {
                        return ty;
                    }
                }
                if let Some(end) = &range.end {
                    if let Some(ty) = StrongType::from(end.as_ref()).some() {
                        return ty;
                    }
                }
                StrongType::Unknown {
                    location: value.span(),
                    reason: "can't infer type from range",
                }
            }
            Pat::Slice(it) => it
                .elems
                .iter()
                .find_map(|it| StrongType::from(it).some())
                .unwrap_or_else(|| StrongType::Unknown {
                    location: value.span(),
                    reason: "can't infer type of any slice elements",
                }),
            Pat::Struct(it) => StrongType::from(match PathKind::guess_for_path(&it.path) {
                Some(PathKind::Variant) => variant_path_to_type(&it.path),
                _ => Type::Path(TypePath {
                    qself: None,
                    path: it.path.clone(),
                }),
            }),
            Pat::Tuple(it) => {
                let types: Vec<_> = it
                    .elems
                    .iter()
                    .filter_map(|it| StrongType::from(it).to_type().ok())
                    .collect();

                // TODO: Support partial tuple inference
                if types.len() != it.elems.len() {
                    return StrongType::Unknown {
                        location: value.span(),
                        reason: "can't infer type of some tuple elements",
                    };
                }

                StrongType::from(Type::Tuple(TypeTuple {
                    paren_token: token::Paren::default(),
                    elems: Punctuated::from_iter(types.into_iter()),
                }))
            }
            Pat::TupleStruct(it) => {
                if it.elems.len() == 1 {
                    if is_ok_path(&it.path) {
                        return StrongType::Result(Box::new(ResultType {
                            ok_ty: StrongType::from(&it.elems[0]),
                            err_ty: StrongType::Unknown {
                                location: value.span(),
                                reason: "can't infer Ok type from Err pattern",
                            },
                            source_span: Some(it.span()),
                        }));
                    }
                    if is_err_path(&it.path) {
                        return StrongType::Result(Box::new(ResultType {
                            ok_ty: StrongType::Unknown {
                                location: value.span(),
                                reason: "can't infer Ok type from Err pattern",
                            },
                            err_ty: StrongType::from(&it.elems[0]),
                            source_span: Some(it.span()),
                        }));
                    }
                    if is_some_path(&it.path) {
                        return StrongType::Option(Box::new(OptionType {
                            some_ty: StrongType::from(&it.elems[0]),
                            source_span: Some(it.span()),
                        }));
                    }
                }

                StrongType::from(match PathKind::guess_for_path(&it.path) {
                    Some(PathKind::Variant) => variant_path_to_type(&it.path),
                    _ => Type::Path(TypePath {
                        qself: None,
                        path: it.path.clone(),
                    }),
                })
            }
            Pat::Type(it) => StrongType::from(it.ty.as_ref()),
            _ => StrongType::Unknown {
                location: value.span(),
                reason: "can't infer type from pattern",
            },
        }
    }
}

impl<'a> From<&'a Block> for StrongType<'a> {
    fn from(value: &'a Block) -> Self {
        // TODO: deeper block expression type inferrence if ident is in scope
        // requires tracking scope for most expressions
        if let Some(last) = value.stmts.last() {
            match last {
                Stmt::Expr(expr, None) => StrongType::from(expr),
                Stmt::Expr(expr, Some(_)) if matches!(expr, Expr::Return(_)) => {
                    StrongType::from(expr)
                }
                Stmt::Macro(it) => StrongType::Unknown {
                    location: it.span(),
                    reason: "can't infer type from unexpanded macro",
                },
                other => StrongType::Unit(other.span()),
            }
        } else {
            StrongType::Unit(value.span())
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
pub enum MatchKind {
    Result,
    Option,
    Other,
}

impl From<&ExprMatch> for MatchKind {
    fn from(value: &ExprMatch) -> Self {
        for arm in &value.arms {
            if ResultPattern::check(&arm.pat) {
                return MatchKind::Result;
            }
            if OptionPattern::check(&arm.pat) {
                return MatchKind::Option;
            }
        }
        MatchKind::Other
    }
}
