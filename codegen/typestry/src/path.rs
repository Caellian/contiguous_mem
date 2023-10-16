// TODO: Optimize consecutive calls to this function
// introduce PathExpression struct, PathMatchSegment enum
// PathMatchSegment can be Exact, OneOf && Optional

use std::cmp;

use syn::{punctuated::Punctuated, Path, Type, TypePath};

pub enum SegmentMatch<'a> {
    Exact(&'a str),
    OneOf(&'a [&'a str]),
    Optional(&'a str),
}

/// Allows matching [`PathSegment`]s against a syn [`Path`](syn::Path).
pub struct PathMatch<'a> {
    pub segments: &'a [SegmentMatch<'a>],
    pub required_length: usize,
}

impl<'a> PathMatch<'a> {
    /// # Examples
    /// ```
    /// use typestry::path::*;
    ///
    /// static RESULT_MATCH: PathMatch<'static> = PathMatch {
    ///     segments: &[
    ///         SegmentMatch::OneOf(&["std", "core"]),
    ///         SegmentMatch::Exact("result"),
    ///         SegmentMatch::Exact("Result"),
    ///     ],
    /// };
    ///
    /// assert!(RESULT_MATCH.check(&syn::parse_quote!(std::result::Result)));
    /// assert!(RESULT_MATCH.check(&syn::parse_quote!(result::Result)));
    /// assert!(RESULT_MATCH.check(&syn::parse_quote!(Result)));
    ///
    /// assert!(!RESULT_MATCH.check(&syn::parse_quote!(std::option::Option)));
    ///
    /// ```
    pub fn check(&self, path: &syn::Path) -> bool {
        let check_count = cmp::min(self.segments.len(), path.segments.len());

        if check_count < self.required_length {
            return false;
        }

        let checked = path.segments.iter().rev().take(check_count);
        let mut current = self.segments.len() - 1;

        for elem in checked {
            match self.segments[current] {
                SegmentMatch::Exact(exact) => {
                    if elem.ident != exact {
                        return false;
                    }
                }
                SegmentMatch::OneOf(one_of) => {
                    if !one_of.iter().any(|it| elem.ident == *it) {
                        return false;
                    }
                }
                SegmentMatch::Optional(opt) => {
                    if elem.ident != opt {
                        continue;
                    }
                }
            }
            current -= 1;
            if current == 0 {
                break;
            }
        }

        true
    }
}

pub(crate) enum PathKind {
    Const,
    Variant,
    Struct,
    Module,
    Function,
    Ident,
}

impl PathKind {
    /// Guesses the kind of provided path. This guess follows Rust naming
    /// conventions most codebases follow.
    pub(crate) fn guess_for_path(path: &Path) -> Option<PathKind> {
        #[inline]
        fn first_upper(of: &str) -> bool {
            of.chars()
                .next()
                .map(|it| it.is_uppercase())
                .unwrap_or_default()
        }

        match path.segments.len() {
            0 => return None,
            1 => {
                let seg = path.segments[0].ident.to_string();

                if seg.is_empty() {
                    return None;
                }

                let all_cap = seg.chars().all(|it| it.is_uppercase());
                let first_cap = first_upper(&seg);

                if all_cap {
                    Some(PathKind::Const)
                } else if first_cap {
                    Some(PathKind::Struct)
                } else {
                    Some(PathKind::Ident)
                }
            }
            _ => {
                let seg_c = path.segments.len();
                let last_seg = path.segments[seg_c - 1].ident.to_string();
                let second_last_seg = path.segments[seg_c - 2].ident.to_string();

                let all_cap = last_seg.chars().all(|it| it.is_uppercase());

                if all_cap {
                    Some(PathKind::Const)
                } else {
                    match (first_upper(&second_last_seg), first_upper(&last_seg)) {
                        (true, true) => Some(PathKind::Variant),
                        (false, true) => Some(PathKind::Struct),
                        (false, false) => Some(PathKind::Module),
                        (true, false) => Some(PathKind::Function),
                    }
                }
            }
        }
    }
}

pub(crate) fn variant_path_to_type(path: &Path) -> Type {
    Type::Path(TypePath {
        qself: None,
        path: Path {
            leading_colon: path.leading_colon.clone(),
            segments: Punctuated::from_iter(
                path.segments.iter().take(path.segments.len() - 1).cloned(),
            ),
        },
    })
}
