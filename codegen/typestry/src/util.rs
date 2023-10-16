use proc_macro2::{Span, TokenTree};
use quote::ToTokens;
use syn::{punctuated::Punctuated, *};

pub trait SyntaxEq<Rhs: ?Sized> {
    fn syntax_eq(&self, other: &Rhs) -> bool;
}

impl<T: ToTokens, Rhs: ToTokens> SyntaxEq<Rhs> for T {
    fn syntax_eq(&self, other: &Rhs) -> bool {
        let left = self.to_token_stream().into_iter();
        let mut right = other.to_token_stream().into_iter();

        // .zip().all() with size check
        for l in left {
            let r = match right.next() {
                Some(it) => it,
                None => return false,
            };

            match (l, r) {
                (TokenTree::Group(a), TokenTree::Group(b)) if a.syntax_eq(&b) => {}
                (TokenTree::Ident(a), TokenTree::Ident(b)) if a.to_string() != b.to_string() => {}
                (TokenTree::Punct(a), TokenTree::Punct(b)) if a.as_char() == b.as_char() => {}
                (TokenTree::Literal(a), TokenTree::Literal(b))
                    if a.to_string() == b.to_string() => {}
                _ => return false,
            }
        }
        true
    }
}

impl<T: ToTokens> SyntaxEq<str> for T {
    fn syntax_eq(&self, other: &str) -> bool {
        self.to_token_stream().to_string() == other
    }
}

#[inline]
pub fn unit_type() -> Type {
    Type::Tuple(TypeTuple {
        paren_token: token::Paren::default(),
        elems: Punctuated::new(),
    })
}

#[inline]
pub fn ty_literal(ty: impl AsRef<str>) -> Type {
    Type::Path(TypePath {
        qself: None,
        path: Path {
            leading_colon: None,
            segments: Punctuated::from_iter(std::iter::once(PathSegment {
                ident: Ident::new(ty.as_ref(), Span::call_site()),
                arguments: PathArguments::None,
            })),
        },
    })
}

#[inline]
pub fn ref_ty_literal(lifetime: Option<Lifetime>, mutable: bool, ty: impl AsRef<str>) -> Type {
    Type::Reference(TypeReference {
        and_token: token::And::default(),
        lifetime,
        mutability: if mutable {
            Some(token::Mut::default())
        } else {
            None
        },
        elem: Box::new(ty_literal(ty)),
    })
}

#[inline]
pub fn lifetime(lifetime: impl AsRef<str>) -> Lifetime {
    Lifetime {
        apostrophe: Span::call_site(),
        ident: Ident::new(lifetime.as_ref(), Span::call_site()),
    }
}

#[inline]
pub fn static_lifetime() -> Lifetime {
    lifetime("static")
}
