//! This module defines path matching rules for some std constants.
//! 
//! 
//! 
//! Create a PR if any new ones are missing or some are omitted.

use std::borrow::Cow;

use syn::spanned::Spanned;

use crate::{
    path::{PathMatch, SegmentMatch},
    util::ty_literal,
    StrongType,
};

macro_rules! float_consts {
    ($of: literal) => {
        PathMatch {
            segments: &[
                SegmentMatch::OneOf(&["std", "core"]),
                SegmentMatch::Exact($of),
                SegmentMatch::Exact("consts"),
                SegmentMatch::OneOf(&[
                    "E",
                    "FRAC_1_PI",
                    "FRAC_1_SQRT_2",
                    "FRAC_2_PI",
                    "FRAC_2_SQRT_PI",
                    "FRAC_PI_2",
                    "FRAC_PI_3",
                    "FRAC_PI_4",
                    "FRAC_PI_6",
                    "FRAC_PI_8",
                    "LN_10",
                    "LN_2",
                    "LOG10_2",
                    "LOG10_E",
                    "LOG2_10",
                    "LOG2_E",
                    "PI",
                    "SQRT_2",
                    "TAU",
                ]),
            ],
            required_length: 3,
        }
    };
}

static F32_CONSTS: PathMatch<'static> = float_consts!("f32");
static F64_CONSTS: PathMatch<'static> = float_consts!("f64");

macro_rules! float_assoc_consts {
    ($of: literal) => {
        PathMatch {
            segments: &[
                SegmentMatch::Exact($of),
                SegmentMatch::OneOf(&[
                    "DIGITS",
                    "EPSILON",
                    "INFINITY",
                    "MANTISSA_DIGITS",
                    "MAX",
                    "MAX_10_EXP",
                    "MAX_EXP",
                    "MIN",
                    "MIN_10_EXP",
                    "MIN_EXP",
                    "MIN_POSITIVE",
                    "NAN",
                    "NEG_INFINITY",
                    "RADIX",
                ]),
            ],
            required_length: 2,
        }
    };
}

static F32_ASSOC_CONSTS: PathMatch<'static> = float_assoc_consts!("f32");
static F64_ASSOC_CONSTS: PathMatch<'static> = float_assoc_consts!("f64");

macro_rules! int_assoc_consts {
    ($of: literal) => {
        PathMatch {
            segments: &[
                SegmentMatch::Exact($of),
                SegmentMatch::OneOf(&["BITS", "MIN", "MAX"]),
            ],
            required_length: 2,
        }
    };
}

static U8_ASSOC_CONSTS: PathMatch<'static> = int_assoc_consts!("u8");
static U16_ASSOC_CONSTS: PathMatch<'static> = int_assoc_consts!("u16");
static U32_ASSOC_CONSTS: PathMatch<'static> = int_assoc_consts!("u32");
static U64_ASSOC_CONSTS: PathMatch<'static> = int_assoc_consts!("u64");
static U128_ASSOC_CONSTS: PathMatch<'static> = int_assoc_consts!("u128");
static USIZE_ASSOC_CONSTS: PathMatch<'static> = int_assoc_consts!("usize");

static I8_ASSOC_CONSTS: PathMatch<'static> = int_assoc_consts!("i8");
static I16_ASSOC_CONSTS: PathMatch<'static> = int_assoc_consts!("i16");
static I32_ASSOC_CONSTS: PathMatch<'static> = int_assoc_consts!("i32");
static I64_ASSOC_CONSTS: PathMatch<'static> = int_assoc_consts!("i64");
static I128_ASSOC_CONSTS: PathMatch<'static> = int_assoc_consts!("i128");
static ISIZE_ASSOC_CONSTS: PathMatch<'static> = int_assoc_consts!("isize");

pub(crate) fn const_type(path: &syn::Path) -> StrongType {
    if F32_CONSTS.check(path) || F32_ASSOC_CONSTS.check(path) {
        return StrongType::Other(Cow::Owned(ty_literal("f32")));
    } else if F64_CONSTS.check(path) || F64_ASSOC_CONSTS.check(path) {
        return StrongType::Other(Cow::Owned(ty_literal("f64")));
    }

    static CHECKS: &[(&PathMatch<'static>, &str)] = &[
        (&U8_ASSOC_CONSTS, "u8"),
        (&U16_ASSOC_CONSTS, "u16"),
        (&U32_ASSOC_CONSTS, "u32"),
        (&U64_ASSOC_CONSTS, "u64"),
        (&U128_ASSOC_CONSTS, "u128"),
        (&USIZE_ASSOC_CONSTS, "usize"),
        (&I8_ASSOC_CONSTS, "i8"),
        (&I16_ASSOC_CONSTS, "i16"),
        (&I32_ASSOC_CONSTS, "i32"),
        (&I64_ASSOC_CONSTS, "i64"),
        (&I128_ASSOC_CONSTS, "i128"),
        (&ISIZE_ASSOC_CONSTS, "isize"),
    ];

    for check in CHECKS {
        if check.0.check(path) {
            return StrongType::Other(Cow::Owned(ty_literal(check.1)));
        }
    }

    return StrongType::Unknown {
        location: path.span(),
        reason: "can't infer path type",
    };
}
