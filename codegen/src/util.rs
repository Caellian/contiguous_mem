use proc_macro2::Span;
use quote::ToTokens;
use syn::{
    punctuated::{Pair, Punctuated},
    spanned::Spanned,
    token::{Return, Underscore},
    *,
};

pub fn type_path_ends_with(tp: &TypePath, name: impl AsRef<str>) -> bool {
    if let Some(last) = tp.path.segments.last() {
        let ident = last.ident.to_string();
        ident.ends_with(name.as_ref())
    } else {
        false
    }
}

pub fn get_result_ok_err(path: &mut Path) -> Option<(&mut Type, Option<&mut Type>)> {
    if let Some(last) = path.segments.last_mut() {
        let generic_args = match &mut last.arguments {
            PathArguments::AngleBracketed(a) => &mut a.args,
            _ => return None,
        };

        if generic_args.len() > 1 {
            let mut generic_args = generic_args.iter_mut().filter_map(|it| match it {
                GenericArgument::Type(ty) => Some(ty),
                _ => None,
            });

            return Some((generic_args.next().unwrap(), generic_args.next()));
        }
    }
    None
}

#[repr(transparent)]
pub struct TokenEq<'a>(pub &'a dyn ToTokens);

impl<'a> From<&'a dyn ToTokens> for TokenEq<'a> {
    #[inline]
    fn from(value: &'a dyn ToTokens) -> Self {
        TokenEq(value)
    }
}

impl PartialEq for TokenEq<'_> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0.to_token_stream().to_string() == other.0.to_token_stream().to_string()
    }
}

impl<S: AsRef<str>> PartialEq<S> for TokenEq<'_> {
    #[inline]
    fn eq(&self, other: &S) -> bool {
        self.0.to_token_stream().to_string() == other.as_ref()
    }
}

#[repr(transparent)]
pub struct Destructure<T>(pub T);

impl<E: AsRef<Expr>> PartialEq<Ident> for Destructure<E> {
    #[inline]
    fn eq(&self, other: &Ident) -> bool {
        match self.0.as_ref() {
            Expr::Path(ExprPath { path, .. }) if path.segments.len() == 1 => {
                let segment = path.segments.first().unwrap();
                segment.ident == *other
            }
            _ => false,
        }
    }
}
impl<E: AsRef<Expr>> PartialEq<&str> for Destructure<E> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        match self.0.as_ref() {
            Expr::Path(ExprPath { path, .. }) if path.segments.len() == 1 => {
                let segment = path.segments.first().unwrap();
                segment.ident == *other
            }
            _ => false,
        }
    }
}

impl Into<Type> for Destructure<&ReturnType> {
    fn into(self) -> Type {
        match self.0 {
            ReturnType::Default => unit_type(),
            ReturnType::Type(_, ty) => ty.as_ref().clone(),
        }
    }
}

impl<'a> Into<Option<&'a [Attribute]>> for Destructure<&'a Pat> {
    fn into(self) -> Option<&'a [Attribute]> {
        let attrs = match self.0 {
            Pat::Const(it) => &it.attrs,
            Pat::Ident(it) => &it.attrs,
            Pat::Lit(it) => &it.attrs,
            Pat::Macro(it) => &it.attrs,
            Pat::Or(it) => &it.attrs,
            Pat::Paren(it) => &it.attrs,
            Pat::Path(it) => &it.attrs,
            Pat::Range(it) => &it.attrs,
            Pat::Reference(it) => &it.attrs,
            Pat::Rest(it) => &it.attrs,
            Pat::Slice(it) => &it.attrs,
            Pat::Struct(it) => &it.attrs,
            Pat::Tuple(it) => &it.attrs,
            Pat::TupleStruct(it) => &it.attrs,
            Pat::Type(it) => &it.attrs,
            Pat::Wild(it) => &it.attrs,
            _ => return None,
        };

        if attrs.len() > 0 {
            Some(attrs)
        } else {
            None
        }
    }
}

pub trait CallSiteDefault {
    fn call_site_default() -> Self;
}
impl CallSiteDefault for token::PathSep {
    fn call_site_default() -> Self {
        token::PathSep {
            spans: [Span::call_site(), Span::call_site()],
        }
    }
}

pub trait StartsWithExt {
    fn starts_with(&self, other: &Self) -> bool;
}

impl<'a, T: ToTokens, P> StartsWithExt for Punctuated<T, P> {
    #[inline]
    fn starts_with(&self, other: &Self) -> bool {
        other
            .iter()
            .zip(self.iter())
            .all(|(a, b)| TokenEq(a) == TokenEq(b))
    }
}

impl StartsWithExt for Path {
    #[inline]
    fn starts_with(&self, other: &Self) -> bool {
        self.leading_colon.is_some() == other.leading_colon.is_some()
            && self.segments.starts_with(&other.segments)
    }
}

pub trait ReplacePunctExt<'a, T: ToTokens> {
    fn replace(
        &mut self,
        old: impl IntoIterator<Item = &'a T>,
        new: &(impl IntoIterator<Item = T> + Clone),
    ) where
        T: 'a;
    fn replace_all(
        &mut self,
        old: impl IntoIterator<Item = &'a T>,
        new: &(impl IntoIterator<Item = T> + Clone),
    ) where
        T: 'a;
    fn replace_start(
        &mut self,
        old: impl IntoIterator<Item = &'a T>,
        new: &(impl IntoIterator<Item = T> + Clone),
    ) where
        T: 'a;
    fn replace_end(
        &mut self,
        old: impl IntoIterator<Item = &'a T>,
        new: &(impl IntoIterator<Item = T> + Clone),
    ) where
        T: 'a;
}

fn replace_fn<'a, T: ToTokens + Clone, const FIRST_ONLY: bool>(
    result: &mut Vec<T>,
    old: Vec<&'a T>,
    new: &(impl IntoIterator<Item = T> + Clone),
) {
    for i in 0..result.len() {
        let mut match_found = true;

        // Check if there is a potential match for the old starting at this position
        for (j, search_item) in old.iter().enumerate() {
            if i + j >= result.len() || TokenEq(&result[i + j]) != TokenEq(&search_item) {
                match_found = false;
                break;
            }
        }

        // If a match is found, replace the elements and update the loop index
        if match_found {
            result.splice(i..i + old.len(), new.clone().into_iter());
            if FIRST_ONLY {
                break;
            }
        }
    }
}

impl<'a, T: ToTokens + Clone, P: Default + Clone> ReplacePunctExt<'a, T> for Punctuated<T, P> {
    fn replace(
        &mut self,
        old: impl IntoIterator<Item = &'a T>,
        new: &(impl IntoIterator<Item = T> + Clone),
    ) where
        T: 'a,
    {
        let mut result_vec: Vec<T> = self
            .clone()
            .into_pairs()
            .map(|it| it.into_value())
            .collect(); // Clone the input Vec to start with

        let old: Vec<&T> = old.into_iter().collect();

        if old.len() > result_vec.len() {
            return;
        }

        replace_fn::<T, true>(&mut result_vec, old, new);

        self.clear();
        for entry in result_vec {
            self.push(entry.clone());
        }
    }

    fn replace_all(
        &mut self,
        old: impl IntoIterator<Item = &'a T>,
        new: &(impl IntoIterator<Item = T> + Clone),
    ) where
        T: 'a,
    {
        let mut result_vec: Vec<T> = self
            .clone()
            .into_pairs()
            .map(|it| it.into_value())
            .collect(); // Clone the input Vec to start with

        let old: Vec<&T> = old.into_iter().collect();
        if old.len() > result_vec.len() {
            return;
        }

        replace_fn::<T, false>(&mut result_vec, old, new);

        self.clear();
        for entry in result_vec {
            self.push(entry.clone());
        }
    }

    fn replace_start(
        &mut self,
        old: impl IntoIterator<Item = &'a T>,
        new: &(impl IntoIterator<Item = T> + Clone),
    ) where
        T: 'a,
    {
        let mut result_vec: Vec<T> = self
            .clone()
            .into_pairs()
            .map(|it| it.into_value())
            .collect(); // Clone the input Vec to start with

        let old: Vec<&T> = old.into_iter().collect();
        if old.len() > result_vec.len() {
            return;
        }

        let mut match_found = true;

        // Check if the input starts with the old using fuzzy_eq
        for (i, item) in old.iter().enumerate() {
            if i >= result_vec.len() || TokenEq(item) != TokenEq(&result_vec[i]) {
                match_found = false;
                break;
            }
        }

        // If a match is found, replace the elements
        if match_found {
            result_vec.splice(0..old.len(), new.clone().into_iter());
        }

        self.clear();
        for entry in result_vec {
            self.push(entry.clone());
        }
    }

    fn replace_end(
        &mut self,
        old: impl IntoIterator<Item = &'a T>,
        new: &(impl IntoIterator<Item = T> + Clone),
    ) where
        T: 'a,
    {
        let mut result_vec: Vec<T> = self
            .clone()
            .into_pairs()
            .map(|it| it.into_value())
            .collect(); // Clone the input Vec to start with

        let old: Vec<&T> = old.into_iter().collect();

        if old.len() > result_vec.len() {
            return;
        }

        let mut match_found = true;

        // Check if the input ends with the old using fuzzy_eq
        for (i, item) in old.iter().enumerate() {
            let input_index = result_vec.len() - old.len() + i;
            if TokenEq(item) != TokenEq(&result_vec[input_index]) {
                match_found = false;
                break;
            }
        }

        // If a match is found, replace the elements
        if match_found {
            let start_index = result_vec.len() - old.len();
            result_vec.splice(start_index.., new.clone().into_iter());
        }

        self.clear();
        for entry in result_vec {
            self.push(entry.clone());
        }
    }
}

pub trait SplitPunctExt: Sized {
    fn split(self, index: usize) -> (Self, Self);
}

impl<T, P> SplitPunctExt for Punctuated<T, P> {
    fn split(self, index: usize) -> (Self, Self) {
        let mut first_half: Vec<Pair<T, P>> = self.into_pairs().collect();
        let second_half = first_half.split_off(index);
        if let Some(it) = first_half.pop() {
            first_half.push(Pair::End(it.into_value()));
        }

        (
            Punctuated::from_iter(first_half),
            Punctuated::from_iter(second_half),
        )
    }
}

#[inline]
pub fn ident_path(ident: Ident) -> Path {
    Path {
        leading_colon: None,
        segments: Punctuated::from_iter(std::iter::once(PathSegment {
            ident,
            arguments: PathArguments::None,
        })),
    }
}

#[inline]
pub fn ident(value: impl AsRef<str>) -> Ident {
    Ident::new(value.as_ref(), Span::call_site())
}

#[inline]
pub fn unit_tuple() -> ExprTuple {
    ExprTuple {
        attrs: vec![],
        paren_token: token::Paren::default(),
        elems: Punctuated::new(),
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
pub unsafe fn reset_lifetime_mut<'a, 'b, T>(value: &'a mut T) -> &'b mut T {
    &mut *(value as *mut T)
}

#[inline]
pub unsafe fn reset_lifetime<'a, 'b, T>(value: &'a T) -> &'b T {
    &*(value as *const T)
}
