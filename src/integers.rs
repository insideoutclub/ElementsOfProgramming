// integers.h

// Copyright (c) 2009 Alexander Stepanov and Paul McJones
//
// Permission to use, copy, modify, distribute and sell this software
// and its documentation for any purpose is hereby granted without
// fee, provided that the above copyright notice appear in all copies
// and that both that copyright notice and this permission notice
// appear in supporting documentation. The authors make no
// representations about the suitability of this software for any
// purpose. It is provided "as is" without express or implied
// warranty.

// Implementation for integral types of special-case Integer procedures from
// Elements of Programming
// by Alexander Stepanov and Paul McJones
// Addison-Wesley Professional, 2009

use num::{NumCast, One, Zero};
use std::ops::{BitAnd, Div, Rem, Shl, Shr, Sub};

pub trait Regular: Clone + Default + Eq {
    type UnderlyingType;
}

impl Regular for i32 {
    type UnderlyingType = i32;
}

impl Regular for usize {
    type UnderlyingType = usize;
}

pub trait Integer:
    BitAnd<Self, Output = Self>
    + Div<Self, Output = Self>
    + NumCast
    + One
    + Ord
    + Regular
    + Rem<Self, Output = Self>
    + Shl<Self, Output = Self>
    + Shr<Self, Output = Self>
    + Sub<Self, Output = Self>
    + Zero
{
    fn two() -> Self;
}

impl<I> Integer for I
where
    I: BitAnd<I, Output = I>
        + Div<I, Output = I>
        + NumCast
        + One
        + Ord
        + Regular
        + Rem<I, Output = I>
        + Shl<I, Output = I>
        + Shr<I, Output = I>
        + Sub<I, Output = I>
        + Zero,
{
    fn two() -> Self {
        NumCast::from(2).unwrap()
    }
}

// Exercise 3.2

pub fn successor<I>(a: I) -> I
where
    I: Integer,
{
    a + I::one()
}

pub fn predecessor<I>(a: I) -> I
where
    I: Integer,
{
    a - I::one()
}

pub fn twice<I>(a: I) -> I
where
    I: Integer,
{
    a.clone() + a
}

pub fn half_nonnegative<I>(a: I) -> I
where
    I: Integer,
{
    a >> I::one()
}

pub fn _binary_scale_down_nonnegative<I>(a: I, k: I) -> I
where
    I: Integer,
{
    a >> k
}

pub fn binary_scale_up_nonnegative<I>(a: I, k: I) -> I
where
    I: Integer,
{
    a << k
}

pub fn _positive<I>(a: &I) -> bool
where
    I: Integer,
{
    I::zero() < *a
}

pub fn _negative<I>(a: &I) -> bool
where
    I: Integer,
{
    *a < I::zero()
}

pub fn zero<I>(a: &I) -> bool
where
    I: Integer,
{
    a == &I::zero()
}

pub fn one<I>(a: &I) -> bool
where
    I: Integer,
{
    a == &I::one()
}

pub fn even<I>(a: I) -> bool
where
    I: Integer,
{
    a & I::one() == I::zero()
}

pub fn odd<I>(a: I) -> bool
where
    I: Integer,
{
    a & I::one() != I::zero()
}

// Chapter 5: definition of half for Integer types, to model HalvableMonoid:

pub fn _half<I>(x: I) -> I
where
    I: Integer,
{
    half_nonnegative(x)
}
