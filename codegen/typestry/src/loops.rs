use proc_macro2::Span;
use syn::{spanned::Spanned, *};

use super::StrongType;

#[derive(Clone, Copy)]
struct LoopBlock<'a> {
    block: &'a Block,
    label: Option<&'a Ident>,
    span: Span,
}

fn loop_expr_result<'a>(expr: &'a Expr, label: Option<&'a Ident>) -> Option<&'a Expr> {
    if let Expr::Break(it) = expr {
        if it.label.as_ref().map(|it| it.ident.to_string()) == label.map(|it| it.to_string()) {
            return it.expr.as_ref().map(|it| it.as_ref());
        }
    }

    match expr {
        Expr::Group(ExprGroup { expr, .. }) | Expr::Paren(ExprParen { expr, .. }) => {
            loop_expr_result(expr.as_ref(), label)
        }

        Expr::Block(ExprBlock { block, .. })
        | Expr::TryBlock(ExprTryBlock { block, .. })
        | Expr::Unsafe(ExprUnsafe { block, .. }) => loop_block_result(block, label),

        Expr::If(ExprIf {
            then_branch,
            else_branch,
            ..
        }) => loop_block_result(then_branch, label).or_else(|| {
            else_branch
                .as_ref()
                .map(|(_, it)| loop_expr_result(it.as_ref(), label))
                .flatten()
        }),
        Expr::Match(it) => it
            .arms
            .iter()
            .find_map(|arm| loop_expr_result(arm.body.as_ref(), label)),

        Expr::ForLoop(ExprForLoop { body, .. })
        | Expr::Loop(ExprLoop { body, .. })
        | Expr::While(ExprWhile { body, .. })
            if label.is_some() =>
        {
            loop_block_result(body, label)
        }

        _ => None,
    }
}

#[inline]
fn loop_block_result<'a>(block: &'a Block, label: Option<&'a Ident>) -> Option<&'a Expr> {
    block
        .stmts
        .iter()
        .filter_map(|it| match it {
            Stmt::Expr(expr, _) => Some(expr),
            _ => None,
        })
        .find_map(|expr| loop_expr_result(expr, label))
}

impl<'a> LoopBlock<'a> {
    pub fn value_expr(&self) -> Option<&'a Expr> {
        loop_block_result(self.block, self.label)
    }
}

impl<'a> From<&'a ExprLoop> for LoopBlock<'a> {
    fn from(value: &'a ExprLoop) -> Self {
        LoopBlock {
            block: &value.body,
            label: value.label.as_ref().map(|it| &it.name.ident),
            span: value.span(),
        }
    }
}

impl<'a> From<&'a ExprForLoop> for LoopBlock<'a> {
    fn from(value: &'a ExprForLoop) -> Self {
        LoopBlock {
            block: &value.body,
            label: value.label.as_ref().map(|it| &it.name.ident),
            span: value.span(),
        }
    }
}

impl<'a> From<&'a ExprWhile> for LoopBlock<'a> {
    fn from(value: &'a ExprWhile) -> Self {
        LoopBlock {
            block: &value.body,
            label: value.label.as_ref().map(|it| &it.name.ident),
            span: value.span(),
        }
    }
}

impl<'a, L: Into<LoopBlock<'a>>> From<L> for StrongType<'a> {
    fn from(value: L) -> Self {
        let loop_block: LoopBlock<'a> = value.into();
        match loop_block.value_expr() {
            Some(it) => StrongType::from(it),
            None => StrongType::Unit(loop_block.span),
        }
    }
}
