use std::result;

use proc_macro2::Span;
use quote::ToTokens;
use syn::{punctuated::Punctuated, spanned::Spanned, visit_mut::VisitMut, *};
use typestry::{MatchKind, ResultPattern, ResultType, StrongType};

use crate::util::{
    get_result_ok_err, ident_path, reset_lifetime_mut, type_path_ends_with, unit_tuple, unit_type,
    Destructure, ReplacePunctExt, SplitPunctExt, StartsWithExt, TokenEq,
};

pub struct Qualifier {
    pub source: TraitBound,
    pub names: Vec<Ident>,
}

impl Qualifier {
    pub fn new<S: AsRef<str>>(source: TraitBound, names: impl IntoIterator<Item = S>) -> Self {
        Qualifier {
            source,
            names: names
                .into_iter()
                .map(|it| syn::parse_str(it.as_ref()).expect("invalid Qualifier ident"))
                .collect(),
        }
    }

    pub fn apply_to(&self, tp: &mut TypePath, boundary: usize) {
        let path = &mut tp.path;

        if boundary == 0 || path.segments.len() <= boundary {
            return;
        }

        if self
            .names
            .iter()
            .any(|it| *it == path.segments[boundary].ident)
        {
            let (first, mut rest) = path.segments.clone().split(boundary);

            tp.qself = Some(QSelf {
                lt_token: Default::default(),
                ty: Box::new(Type::Path(TypePath {
                    qself: None,
                    path: Path {
                        leading_colon: None,
                        segments: first,
                    },
                })),
                position: 1,
                as_token: Some(Default::default()),
                gt_token: Default::default(),
            });
            rest.insert(
                0,
                syn::parse2(self.source.to_token_stream())
                    .expect("unable to reinterpret trait bound as path segment"),
            );
            tp.path.segments = rest;
        }
    }
}

pub struct SpecializeGenericArg {
    pub source: Path,
    pub target: Path,
    pub qualifiers: Vec<Qualifier>,
}

impl SpecializeGenericArg {
    pub fn new(source: Ident, target: impl AsRef<str>) -> Self {
        SpecializeGenericArg {
            source: ident_path(source),
            target: syn::parse_str(target.as_ref()).expect("invalid SpecializeGenericArg target"),
            qualifiers: vec![],
        }
    }

    pub fn with_qualifier(mut self, qualifier: Qualifier) -> Self {
        self.qualifiers.push(qualifier);
        self
    }
}

impl VisitMut for SpecializeGenericArg {
    fn visit_path_mut(&mut self, node: &mut Path) {
        if node.to_token_stream().to_string() == self.source.to_token_stream().to_string() {
            *node = self.target.clone();
            return;
        } else if node.segments.len() > 1 {
            if node.starts_with(&self.source) {
                node.segments
                    .replace_start(&self.source.segments, &self.target.segments);
                return;
            }
        }

        visit_mut::visit_path_mut(self, node)
    }

    fn visit_type_path_mut(&mut self, tp: &mut TypePath) {
        if tp.path.segments.len() > 1 {
            if tp.path.starts_with(&self.source) {
                tp.path
                    .segments
                    .replace_start(&self.source.segments, &self.target.segments);
                self.qualifiers
                    .iter()
                    .for_each(|q| q.apply_to(tp, self.target.segments.len()));

                return;
            }
        }
        visit_mut::visit_type_path_mut(self, tp)
    }
}

pub struct MapUnwrappedInvocation<'a, S: AsRef<str>> {
    trait_names: &'a [S],
    found_any: bool,
}

impl<'a, S: AsRef<str>> MapUnwrappedInvocation<'a, S> {
    pub fn new(trait_names: &'a [S]) -> Self {
        Self {
            trait_names,
            found_any: false,
        }
    }

    pub fn test_call_fn_path(&self, call: &Expr) -> bool {
        if let Expr::Path(p) = call {
            let segments = &p.path.segments;
            if segments.len() == 2 {
                let trait_test = segments.first().unwrap().ident.to_string();
                return self.trait_names.iter().any(|it| it.as_ref() == trait_test);
            }
        }
        false
    }

    pub fn found(self) -> bool {
        self.found_any
    }

    pub fn within_impl_fn(trait_names: &'a [S], fun: &mut ImplItemFn) -> bool {
        let mut visitor = Self::new(trait_names);

        visitor.visit_impl_item_fn_mut(fun);
        visitor.found()
    }
}

impl<S: AsRef<str>> VisitMut for MapUnwrappedInvocation<'_, S> {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        if let Expr::MethodCall(call) = expr {
            if call.method == "expect" || call.method == "unwrap" {
                if let Expr::Call(call_expr) = call.receiver.as_ref() {
                    if self.test_call_fn_path(call_expr.func.as_ref()) {
                        *expr = Expr::Try(ExprTry {
                            attrs: vec![],
                            expr: Box::new(Expr::Call(call_expr.clone())),
                            question_token: token::Question {
                                spans: [Span::call_site()],
                            },
                        });
                        self.found_any = true;
                        return;
                    }
                }
            }
        }

        visit_mut::visit_expr_mut(self, expr);
    }
}

pub struct ResultMapping<'a> {
    type_map: &'a [(Type, Type)],
    lock_err: Type,
    error: Option<Error>,
}

impl<'a> ResultMapping<'a> {
    pub fn new(type_map: &'a [(Type, Type)], lock_err: Type) -> Self {
        ResultMapping {
            type_map,
            lock_err,
            error: None,
        }
    }

    pub fn result_of(&self, source: Type) -> Type {
        let err_t = &self.lock_err;
        Type::Path(TypePath {
            qself: None,
            path: Path {
                leading_colon: None,
                segments: Punctuated::from_iter([PathSegment {
                    ident: Ident::new("Result", Span::call_site()),
                    arguments: PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                        colon2_token: None,
                        lt_token: token::Lt::default(),
                        args: Punctuated::from_iter([
                            GenericArgument::Type(source),
                            GenericArgument::Type(self.lock_err.clone()),
                        ]),
                        gt_token: token::Gt::default(),
                    }),
                }]),
            },
        })
    }

    pub fn error(self) -> Option<Error> {
        self.error
    }
}

impl VisitMut for ResultMapping<'_> {
    fn visit_return_type_mut(&mut self, ty: &mut ReturnType) {
        match ty {
            ReturnType::Default => {
                *ty = ReturnType::Type(
                    token::RArrow::default(),
                    Box::new(self.result_of(unit_type())),
                );
                return;
            }
            ReturnType::Type(rarrow, rty) => {
                if let Type::Path(tp) = rty.as_mut() {
                    if tp
                        .path
                        .segments
                        .last()
                        .map(|it| it.ident == "Result")
                        .unwrap_or_default()
                    {
                        if let Some((ok_ty, error_ty)) = get_result_ok_err(&mut tp.path) {
                            if let Some(err_ty) = error_ty {
                                if let Some((_, value)) = self
                                    .type_map
                                    .iter()
                                    .find(|(key, _)| TokenEq(key) == TokenEq(err_ty))
                                {
                                    *ty = parse_quote!(#rarrow Result<#ok_ty, #value>);
                                    return;
                                }
                            } else {
                                self.error = Some(Error::new_spanned(
                                    tp,
                                    "partially specified Result types not implemented",
                                ));
                            }
                        }
                    }
                    *rty = Box::new(self.result_of(rty.as_ref().clone()));
                    return;
                }
            }
        }

        visit_mut::visit_return_type_mut(self, ty);
    }
}

pub struct TrySelf<'a> {
    sync_methods: &'a [Signature],
    initial_types: &'a [(Ident, StrongType<'a>)],
    initial_type: StrongType<'a>,
    lock_err: &'a Type,
    in_try: bool,
    found_any: bool,
    error: Option<Error>,
}

impl<'a> TrySelf<'a> {
    fn new_tried(
        sync_methods: &'a [Signature],
        initial_types: &'a [(Ident, StrongType)],
        initial_type: StrongType<'a>,
        lock_err: &'a Type,
    ) -> Self {
        TrySelf {
            sync_methods,
            initial_types,
            initial_type,
            lock_err,
            in_try: true,
            found_any: false,
            error: None,
        }
    }

    pub fn found(self) -> bool {
        self.found_any
    }

    pub fn within_impl_fn(
        sync_methods: &'a [Signature],
        initial_types: &'a [(Ident, StrongType)],
        lock_err: &'a Type,
        fun: &'a mut ImplItemFn,
    ) -> Result<bool> {
        let initial_type = match initial_types
            .iter()
            .find(|(ident, ty)| *ident == fun.sig.ident)
        {
            Some((_, ty)) => ty.clone(),
            None => panic!(
                "unable to find initial type for '{}' function",
                fun.sig.ident.to_string()
            ),
        };
        let mut result = TrySelf {
            sync_methods,
            initial_types,
            initial_type,
            lock_err,
            in_try: false,
            found_any: false,
            error: None,
        };
        result.visit_impl_item_fn_mut(fun);
        if let Some(err) = result.error {
            Err(err)
        } else {
            Ok(result.found_any)
        }
    }
}

fn build_err(pat: &Pat, new_err: &Type) -> Result<Path> {
    fn path_kind(path: &Path, new_err: &Type) -> Result<Ident> {
        let first = match path.segments.first() {
            Some(it) => it,
            None => return Err(Error::new_spanned(path, "missing first segment")),
        };

        match first.ident.to_string().strip_suffix("Error") {
            Some(stripped) => Ok(Ident::new(stripped, first.span())),
            None => {
                return Err(Error::new_spanned(
                    path,
                    format!(
                        "expected an 'Error' suffix on error variant `{}` to construct `{}`",
                        path.to_token_stream().to_string(),
                        new_err.to_token_stream().to_string()
                    ),
                ))
            }
        }
    }

    let sync_attrib = Into::<Option<&[Attribute]>>::into(Destructure(pat)).and_then(|it| {
        it.iter().find_map(|it| match &it.meta {
            Meta::NameValue(MetaNameValue { path, value, .. })
                if TokenEq(&path) == "sync_variant" =>
            {
                Some(value)
            }
            _ => None,
        })
    });

    if let Some(sync_value) = sync_attrib {
        let kind = match sync_value {
            Expr::Path(path) if path.path.segments.len() == 1 => &path.path.segments[0].ident,
            other => {
                return Err(Error::new_spanned(
                    other,
                    format!(
                        "expected a {} variant name",
                        new_err.to_token_stream().to_string()
                    ),
                ));
            }
        };

        return Ok(parse_quote!(#new_err :: #kind));
    }

    let kind = match pat {
        Pat::Path(path) => path_kind(&path.path, &new_err)?,
        Pat::TupleStruct(tuple_struct) => path_kind(&tuple_struct.path, &new_err)?,
        _ => {
            let pat_str = pat.to_token_stream().to_string();
            return Err(Error::new_spanned(
                pat,
                format!("unexpected match pattern: {}", pat_str),
            ));
        }
    };

    Ok(parse_quote!(#new_err :: #kind))
}

fn process_result_arms(arms: &mut Vec<Arm>, new_err: Type) -> Result<()> {
    let has_wild = match arms.last_mut().map(|it| &it.pat) {
        Some(Pat::Wild(_)) => true,
        _ => false,
    };

    let take = if has_wild { arms.len() - 1 } else { arms.len() };

    for arm in arms.iter_mut().take(take) {
        let arm_kind = match ResultPattern::of_pattern(&arm.pat) {
            Some(it) => it,
            None => continue,
        };

        let (err_path, prev_element) = match arm_kind {
            ResultPattern::Err(err) => (build_err(&err, &new_err)?, err),
            _ => continue,
        };

        arm.pat = parse_quote!(Err( #err_path (#prev_element) ));
    }

    arms.insert(
        take,
        parse_quote!(Err( #new_err :: Lock(err) ) => return Err(err),),
    );

    Ok(())
}

impl VisitMut for TrySelf<'_> {
    fn visit_expr_try_mut(&mut self, expr: &mut ExprTry) {
        let mut inner = TrySelf::new_tried(
            self.sync_methods,
            self.initial_types,
            self.initial_type.clone(),
            self.lock_err,
        );
        inner.visit_expr_mut(&mut expr.expr);
        if let Some(err) = inner.error {
            self.error = Some(err);
            return;
        }
        self.found_any |= inner.found();
    }

    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        match expr {
            Expr::Match(match_expr) => {
                // check whether we need to wrap match expressions on own methods

                let called_err_ty: Type = match match_expr.expr.as_ref() {
                    Expr::MethodCall(mc) if Destructure(&mc.receiver) == "self" => {
                        // handle only for synced methods
                        if let Some(sig) = self.sync_methods.iter().find(|it| it.ident == mc.method)
                        {
                            match ResultType::try_from(&Into::<Type>::into(Destructure(
                                &sig.output,
                            ))) {
                                Ok(result_ty) => match result_ty.err_ty.to_type() {
                                    Ok(it) => it,
                                    Err(err) => {
                                        self.error = Some(Error::new_spanned(
                                            &match_expr.expr,
                                            format!(
                                                "unable to infer method Err type: {}{}\nreason: {}",
                                                sig.ident.to_string(),
                                                sig.output.to_token_stream().to_string(),
                                                err
                                            ),
                                        ));
                                        return;
                                    }
                                },
                                Err(err) => {
                                    unreachable!("synced method doesn't return a Result: {}", err)
                                }
                            }
                        } else {
                            // method not synced
                            return visit_mut::visit_expr_mut(self, expr);
                        }
                    }
                    _ => return visit_mut::visit_expr_mut(self, expr),
                };

                let matched_err_ty = match ResultType::try_from(&*match_expr) {
                    Ok(result) => match result.err_ty.to_type() {
                        Ok(it) => it,
                        Err(err) => {
                            self.error = Some(Error::new_spanned(
                                &match_expr.expr,
                                format!("unable to infer current method Err type\nreason: {}", err),
                            ));
                            return;
                        }
                    },
                    _ => {
                        // not matching on result
                        return visit_mut::visit_expr_mut(self, expr);
                    }
                };

                if TokenEq(&called_err_ty) != TokenEq(&matched_err_ty) {
                    // matching on Err that isn't sync, presumably

                    if let Some(err) =
                        process_result_arms(&mut match_expr.arms, called_err_ty).err()
                    {
                        self.error = Some(err);
                    } else {
                        self.found_any = true;
                    };
                    return;
                } else {
                    return visit_mut::visit_expr_mut(self, expr);
                }
            }
            Expr::MethodCall(call) => {
                if Destructure(&call.receiver) == "self" {
                    if self.sync_methods.iter().any(|it| it.ident == call.method) {
                        self.found_any = true;
                        if !self.in_try {
                            let attrs = std::mem::take(&mut call.attrs);
                            let mut inner = Expr::Tuple(unit_tuple());
                            std::mem::swap(&mut inner, expr);
                            *expr = Expr::Try(ExprTry {
                                attrs,
                                expr: Box::new(inner),
                                question_token: token::Question::default(),
                            })
                        }
                        return;
                    }
                }
                visit_mut::visit_expr_method_call_mut(self, call);
            }
            Expr::Try(tried) => self.visit_expr_try_mut(tried),
            other => visit_mut::visit_expr_mut(self, other),
        }
    }
}

pub struct FindReturns<'a> {
    exprs: Vec<&'a mut Expr>,
    error: Option<Error>,
}

impl<'a> FindReturns<'a> {
    #[inline]
    pub fn within_impl_fn(fun: &'a mut ImplItemFn) -> Result<Vec<&'a mut Expr>> {
        let mut result = FindReturns {
            exprs: vec![],
            error: None,
        };
        result.visit_impl_item_fn_mut(fun);
        if let Some(err) = result.error {
            Err(err)
        } else {
            Ok(result.exprs)
        }
    }
}

impl VisitMut for FindReturns<'_> {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        match expr {
            Expr::Return(ExprReturn {
                expr: Some(expr), ..
            }) => unsafe {
                // SAFETY: within_impl_fn defines proper lifetime requirements
                // and expr lifetime can't be specified explicitly.
                self.exprs.push(reset_lifetime_mut(expr));
            },
            other => visit_mut::visit_expr_mut(self, other),
        }
    }

    fn visit_impl_item_fn_mut(&mut self, item: &mut ImplItemFn) {
        #[inline]
        fn test_last_stmt<'a>(stmt: &'a mut Stmt, was_unit: bool) -> Result<&'a mut Expr> {
            let (err_span, found) = match stmt {
                Stmt::Expr(it, None) => return Ok(it),
                Stmt::Expr(it, _) => {
                    if was_unit {
                        return Ok(it);
                    } else {
                        (it.span(), "()")
                    }
                }
                Stmt::Local(it) => (it.span(), "let binding"),
                Stmt::Item(it) => (
                    it.span(),
                    match it {
                        Item::Const(_) => "a const",
                        Item::Enum(_) => "an enum",
                        Item::ExternCrate(_) => "a extern crate",
                        Item::Fn(_) => "a fn",
                        Item::ForeignMod(_) => "a foreign mod",
                        Item::Impl(_) => "a impl",
                        Item::Macro(_) => "a macro",
                        Item::Mod(_) => "a mod",
                        Item::Static(_) => "a static",
                        Item::Struct(_) => "a struct",
                        Item::Trait(_) => "a trait",
                        Item::TraitAlias(_) => "a trait alias",
                        Item::Type(_) => "a type",
                        Item::Union(_) => "a union",
                        Item::Use(_) => "a use",
                        Item::Verbatim(_) => "a verbatim",
                        _ => "something else",
                    },
                ),
                Stmt::Macro(it) => (it.span(), "a macro"),
            };

            Err(Error::new(
                err_span,
                format!(
                    "gen_sync requires expression as the last block statement; found {}",
                    found
                ),
            ))
        }

        let last = match item.block.stmts.last_mut() {
            Some(it) => match test_last_stmt(it, matches!(item.sig.output, ReturnType::Default)) {
                Ok(it) => it,
                Err(err) => {
                    self.error = Some(err);
                    return;
                }
            },
            None => return, // empty impl fn block
        };
        unsafe {
            // SAFETY: same reasoning as visit_expr_mut return
            self.exprs.push(reset_lifetime_mut(last));

            // SAFETY: last stmt is skipped in iterator, so borrowing it for
            // speacial last handling doesn't matter
            let take = item.block.stmts.len() - 1;
            item.block
                .stmts
                .iter_mut()
                .take(take)
                .for_each(|stmt| self.visit_stmt_mut(stmt));
        }
    }
}
