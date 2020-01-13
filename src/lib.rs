// eop.h

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

// Algorithms from
// Elements of Programming
// by Alexander Stepanov and Paul McJones
// Addison-Wesley Professional, 2009

/*#include "assertions.h"
#include "intrinsics.h"
#include "type_functions.h"
#include "pointers.h"
#include "integers.h"
*/
#![deny(clippy::all, clippy::pedantic)]
#![allow(
    clippy::many_single_char_names,
    clippy::too_many_arguments,
    clippy::type_repetition_in_bounds,
    clippy::use_self
)]
use num::{NumCast, One, Zero};
use std::marker::PhantomData;
#[macro_use]
extern crate typenum;
use typenum::{private::IsLessPrivate, Cmp, Compare, False, IsLess, True, P1, P2, P3, P4, Z0};

mod assertions;
use assertions::assert;
mod integers;
mod intrinsics;
use integers::{
    binary_scale_up_nonnegative, even, half_nonnegative, odd, one, predecessor, successor, twice,
    zero, Integer, Regular,
};

//
//  Chapter 1. Foundations
//
#[must_use]
pub fn plus_0(a: i32, b: i32) -> i32 {
    a + b
}

#[must_use]
pub fn plus_1(a: /*&*/ i32, b: /*&*/ i32) -> i32 {
    a + b
}

pub fn plus_2(a: i32, b: i32, c: &mut i32) {
    *c = a + b;
}

#[must_use]
pub fn square(n: i32) -> i32 {
    n * n
}

pub trait BinaryOperation: Regular {
    type Domain: Regular;
    fn call(&self, x: &Self::Domain, y: &Self::Domain) -> Self::Domain;
}

pub fn square_1<Op>(x: &Op::Domain, op: &Op) -> Op::Domain
where
    Op: BinaryOperation,
{
    op.call(x, x)
}

// Function object for equality

#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct Equal<T>(PhantomData<T>);

pub trait Procedure {
    type InputType;
}

impl<T> Relation for Equal<T>
where
    T: Regular,
{
    type Domain = T;
    fn call(&self, x: &T, y: &T) -> bool {
        x == y
    }
}

impl<T> Procedure for (Equal<T>, Z0) {
    type InputType = T;
}

// type pair (see chapter 12 of Elements of Programming)

pub trait TotallyOrdered: Ord {}
impl<T> TotallyOrdered for T where T: Ord {}

#[derive(Clone, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Pair<T0, T1>
where
    T0: Regular,
    T1: Regular,
{
    m0: T0,
    m1: T1,
}

impl<T0, T1> Pair<T0, T1>
where
    T0: Regular,
    T1: Regular,
{
    fn new(m0: T0, m1: T1) -> Self {
        Self { m0, m1 }
    }
}

// type triple (see Exercise 12.2 of Elements of Programming)

#[derive(Clone, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Triple<T0, T1, T2>
where
    T0: Regular,
    T1: Regular,
    T2: Regular,
{
    m0: T0,
    m1: T1,
    m2: T2,
}

impl<T0, T1, T2> Triple<T0, T1, T2>
where
    T0: Regular,
    T1: Regular,
    T2: Regular,
{
    fn new(m0: T0, m1: T1, m2: T2) -> Self {
        Self { m0, m1, m2 }
    }
}

//
//  Chapter 2. Transformations and their orbits
//

//int abs(int x) {
//    if (x < 0) return -x; else return x;
//} // unary operation

#[must_use]
pub fn euclidean_norm(x: f64, y: f64) -> f64 {
    (x * x + y * y).sqrt()
} // binary operation

#[must_use]
pub fn euclidean_norm_3(x: f64, y: f64, z: f64) -> f64 {
    (x * x + y * y + z * z).sqrt()
} // ternary operation

pub trait Transformation {
    type Domain: Regular;
    type DistanceType: Integer;
    fn call(&self, x: Self::Domain) -> Self::Domain;
}

pub fn power_unary<F, N>(mut x: F::Domain, mut n: N, f: &F) -> F::Domain
where
    F: Transformation,
    N: Integer,
{
    // Precondition:
    // $n \geq 0 \wedge (\forall i \in N)\,0 < i \leq n \Rightarrow f^i(x)$ is defined
    while n != N::zero() {
        n = n - N::one();
        x = f.call(x);
    }
    x
}

pub fn distance<F>(mut x: F::Domain, y: &F::Domain, f: &F) -> F::DistanceType
where
    F: Transformation,
{
    // Precondition: $y$ is reachable from $x$ under $f$
    let mut n = F::DistanceType::zero();
    while x != *y {
        x = f.call(x);
        n = n + F::DistanceType::one();
    }
    n
}

pub trait UnaryPredicate {
    type Domain;
    fn call(&self, x: &Self::Domain) -> bool;
}

pub fn collision_point<F, P>(x: F::Domain, f: &F, p: &P) -> F::Domain
where
    F: Transformation,
    P: UnaryPredicate<Domain = F::Domain>,
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    if !p.call(&x) {
        return x;
    }
    let mut slow = x.clone(); // $slow = f^0(x)$
    let mut fast = f.call(x); // $fast = f^1(x)$
                              // $n \gets 0$ (completed iterations)
    while fast != slow {
        // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
        slow = f.call(slow); // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 1}(x)$
        if !p.call(&fast) {
            return fast;
        }
        fast = f.call(fast); // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 2}(x)$
        if !p.call(&fast) {
            return fast;
        }
        fast = f.call(fast); // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 3}(x)$
                             // $n \gets n + 1$
    }
    fast // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
         // Postcondition: return value is terminal point or collision point
}

pub fn terminating<F, P>(x: F::Domain, f: &F, p: &P) -> bool
where
    F: Transformation,
    P: UnaryPredicate<Domain = F::Domain>,
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    !p.call(&collision_point(x, f, p))
}

pub fn collision_point_nonterminating_orbit<F>(x: F::Domain, f: &F) -> F::Domain
where
    F: Transformation,
{
    let mut slow = x.clone(); // $slow = f^0(x)$
    let mut fast = f.call(x); // $fast = f^1(x)$
                              // $n \gets 0$ (completed iterations)
    while fast != slow {
        // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
        slow = f.call(slow); // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 1}(x)$
        fast = f.call(fast); // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 2}(x)$
        fast = f.call(fast); // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 3}(x)$
                             // $n \gets n + 1$
    }
    fast // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
         // Postcondition: return value is collision point
}

pub fn circular_nonterminating_orbit<F>(x: &F::Domain, f: &F) -> bool
where
    F: Transformation,
{
    x == &f.call(collision_point_nonterminating_orbit(x.clone(), f))
}

pub fn circular<F, P>(x: &F::Domain, f: &F, p: &P) -> bool
where
    F: Transformation,
    P: UnaryPredicate<Domain = F::Domain>,
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    let y = collision_point(x.clone(), f, p);
    p.call(&y) && x == &f.call(y)
}

pub fn convergent_point<F>(mut x0: F::Domain, mut x1: F::Domain, f: &F) -> F::Domain
where
    F: Transformation,
{
    // Precondition: $(\exists n \in \func{DistanceType}(F))\,n \geq 0 \wedge f^n(x0) = f^n(x1)$
    while x0 != x1 {
        x0 = f.call(x0);
        x1 = f.call(x1);
    }
    x0
}

pub fn connection_point_nonterminating_orbit<F>(x: F::Domain, f: &F) -> F::Domain
where
    F: Transformation,
{
    convergent_point(
        x.clone(),
        f.call(collision_point_nonterminating_orbit(x, f)),
        f,
    )
}

pub fn connection_point<F, P>(x: F::Domain, f: &F, p: &P) -> F::Domain
where
    F: Transformation,
    P: UnaryPredicate<Domain = F::Domain>,
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    let y = collision_point(x.clone(), f, p);
    if !p.call(&y) {
        return y;
    }
    convergent_point(x, f.call(y), f)
}

// Exercise 2.3:

pub fn convergent_point_guarded<F>(
    mut x0: F::Domain,
    mut x1: F::Domain,
    y: &F::Domain,
    f: &F,
) -> F::Domain
where
    F: Transformation,
{
    // Precondition: $\func{reachable}(x0, y, f) \wedge \func{reachable}(x1, y, f)$
    let d0 = distance(x0.clone(), y, f);
    let d1 = distance(x1.clone(), y, f);
    match d0.cmp(&d1) {
        std::cmp::Ordering::Less => x1 = power_unary(x1, d1 - d0, f),
        std::cmp::Ordering::Greater => x0 = power_unary(x0, d0 - d1, f),
        _ => (),
    }
    convergent_point(x0, x1, f)
}

pub fn orbit_structure_nonterminating_orbit<F>(
    x: F::Domain,
    f: &F,
) -> Triple<F::DistanceType, F::DistanceType, F::Domain>
where
    F: Transformation,
{
    let y = connection_point_nonterminating_orbit(x.clone(), f);
    Triple::new(distance(x, &y, f), distance(f.call(y.clone()), &y, f), y)
}

pub fn orbit_structure<F, P>(
    x: F::Domain,
    f: &F,
    p: &P,
) -> Triple<F::DistanceType, F::DistanceType, F::Domain>
where
    F: Transformation,
    P: UnaryPredicate<Domain = F::Domain>,
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    let y = connection_point(x.clone(), f, p);
    let m = distance(x, &y, f);
    let mut n = F::DistanceType::zero();
    if p.call(&y) {
        n = distance(f.call(y.clone()), &y, f);
    }
    // Terminating: $m = h - 1 \wedge n = 0$
    // Otherwise:   $m = h \wedge n = c - 1$
    Triple::new(m, n, y)
}

//
//  Chapter 3. Associative operations
//

pub fn power_left_associated<I, Op>(a: Op::Domain, n: I, op: &Op) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $n > 0$
    if n == I::one() {
        return a;
    }
    op.call(&power_left_associated(a.clone(), n - I::one(), op), &a)
}

pub fn power_right_associated<I, Op>(a: Op::Domain, n: I, op: &Op) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $n > 0$
    if n == I::one() {
        return a;
    }
    op.call(&a.clone(), &power_right_associated(a, n - I::one(), op))
}

pub fn power_0<I, Op>(a: Op::Domain, n: I, op: &Op) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    if n == I::one() {
        return a;
    }
    if n.clone() % I::two() == I::zero() {
        return power_0(op.call(&a, &a), n / I::two(), op);
    }
    op.call(&power_0(op.call(&a, &a), n / I::two(), op), &a)
}

pub fn power_1<I, Op>(a: Op::Domain, n: I, op: &Op) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    if n == I::one() {
        return a;
    }
    let mut r = power_1(op.call(&a, &a), n.clone() / I::two(), op);
    if n % I::two() != I::zero() {
        r = op.call(&r, &a);
    }
    r
}

pub fn power_accumulate_0<I, Op>(mut r: Op::Domain, a: &Op::Domain, n: I, op: &Op) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if n == I::zero() {
        return r;
    }
    if n.clone() % I::two() != I::zero() {
        r = op.call(&r, a);
    }
    power_accumulate_0(r, &op.call(a, a), n / I::two(), op)
}

pub fn power_accumulate_1<I, Op>(mut r: Op::Domain, a: &Op::Domain, n: I, op: &Op) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if n == I::zero() {
        return r;
    }
    if n == I::one() {
        return op.call(&r, a);
    }
    if n.clone() % I::two() != I::zero() {
        r = op.call(&r, a);
    }
    power_accumulate_1(r, &op.call(a, a), n / I::two(), op)
}

pub fn power_accumulate_2<I, Op>(mut r: Op::Domain, a: &Op::Domain, n: I, op: &Op) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if n.clone() % I::two() != I::zero() {
        r = op.call(&r, a);
        if n == I::one() {
            return r;
        }
    } else if n == I::zero() {
        return r;
    }
    power_accumulate_2(r, &op.call(a, a), n / I::two(), op)
}

pub fn power_accumulate_3<I, Op>(
    mut r: Op::Domain,
    mut a: Op::Domain,
    mut n: I,
    op: &Op,
) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if n.clone() % I::two() != I::zero() {
        r = op.call(&r, &a);
        if n == I::one() {
            return r;
        }
    } else if n == I::zero() {
        return r;
    }
    a = op.call(&a, &a);
    n = n / I::two();
    power_accumulate_3(r, a, n, op)
}

pub fn power_accumulate_4<I, Op>(
    mut r: Op::Domain,
    mut a: Op::Domain,
    mut n: I,
    op: &Op,
) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    loop {
        if n.clone() % I::two() != I::zero() {
            r = op.call(&r, &a);
            if n == I::one() {
                return r;
            }
        } else if n == I::zero() {
            return r;
        }
        a = op.call(&a, &a);
        n = n / I::two();
    }
}

pub fn power_accumulate_positive_0<I, Op>(
    mut r: Op::Domain,
    mut a: Op::Domain,
    mut n: I,
    op: &Op,
) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    loop {
        if n.clone() % I::two() != I::zero() {
            r = op.call(&r, &a);
            if n == I::one() {
                return r;
            }
        }
        a = op.call(&a, &a);
        n = n / I::two();
    }
}

pub fn power_accumulate_5<I, Op>(r: Op::Domain, a: Op::Domain, n: I, op: &Op) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if n == I::zero() {
        return r;
    }
    power_accumulate_positive_0(r, a, n, op)
}

pub fn power_2<I, Op>(a: Op::Domain, n: I, op: &Op) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    power_accumulate_5(a.clone(), a, n - I::one(), op)
}

pub fn power_3<I, Op>(mut a: Op::Domain, mut n: I, op: &Op) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    while n.clone() % I::two() == I::zero() {
        a = op.call(&a, &a);
        n = n / I::two();
    }
    n = n / I::two();
    if n == I::zero() {
        return a;
    }
    let op_a_a = op.call(&a, &a);
    power_accumulate_positive_0(a, op_a_a, n, op)
}

pub fn power_accumulate_positive<I, Op>(
    mut r: Op::Domain,
    mut a: Op::Domain,
    mut n: I,
    op: &Op,
) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge \func{positive}(n)$
    loop {
        if odd(n.clone()) {
            r = op.call(&r, &a);
            if one(&n) {
                return r;
            }
        }
        a = op.call(&a, &a);
        n = half_nonnegative(n);
    }
}

pub fn power_accumulate<I, Op>(r: Op::Domain, a: Op::Domain, n: I, op: &Op) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge \neg \func{negative}(n)$
    if zero(&n) {
        return r;
    }
    power_accumulate_positive(r, a, n, op)
}

pub fn power<I, Op>(mut a: Op::Domain, mut n: I, op: &Op) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge \func{positive}(n)$
    while even(n.clone()) {
        a = op.call(&a, &a);
        n = half_nonnegative(n);
    }
    n = half_nonnegative(n);
    if zero(&n) {
        return a;
    }
    let op_a_a = op.call(&a, &a);
    power_accumulate_positive(a, op_a_a, n, op)
}

pub fn power_4<I, Op>(a: Op::Domain, n: I, op: &Op, id: Op::Domain) -> Op::Domain
where
    I: Integer,
    Op: BinaryOperation,
{
    // Precondition: $\func{associative}(op) \wedge \neg \func{negative}(n)$
    if zero(&n) {
        return id;
    }
    power(a, n, op)
}

#[derive(Clone, Default, Eq, PartialEq)]
pub struct FibonacciMatrixMultiply<I>(PhantomData<I>);

impl<I> BinaryOperation for FibonacciMatrixMultiply<I>
where
    I: Integer,
{
    type Domain = Pair<I, I>;
    fn call(&self, x: &Self::Domain, y: &Self::Domain) -> Self::Domain {
        Pair::new(
            x.m0.clone() * (y.m1.clone() + y.m0.clone()) + x.m1.clone() * y.m0.clone(),
            x.m0.clone() * y.m0.clone() + x.m1.clone() * y.m1.clone(),
        )
    }
}

pub fn fibonacci<I>(n: I) -> I
where
    I: Integer,
{
    // Precondition: $n \geq 0$
    if n == I::zero() {
        return I::zero();
    };
    power(
        Pair::new(I::one(), I::zero()),
        n,
        &FibonacciMatrixMultiply::default(),
    )
    .m0
}

//
//  Chapter 4. Linear orderings
//

// Exercise 4.1: Give an example of a relation that is neither strict nor reflexive
// Exercise 4.2: Give an example of a symmetric relation that is not transitive
// Exercise 4.3: Give an example of a symmetric relation that is not reflexive

pub trait Relation: Regular {
    type Domain;
    fn call(&self, x: &Self::Domain, y: &Self::Domain) -> bool;
}

#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct Complement<R>
where
    R: Relation,
{
    r: R,
}

impl<R> Complement<R>
where
    R: Relation,
{
    fn _new(r: R) -> Self {
        Self { r }
    }
}

impl<R> Relation for Complement<R>
where
    R: Relation,
{
    type Domain = R::Domain;
    fn call(&self, x: &Self::Domain, y: &Self::Domain) -> bool {
        !self.r.call(x, y)
    }
}

impl<R> Procedure for (Complement<R>, Z0)
where
    R: Relation,
{
    type InputType = R::Domain;
}

#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct Converse<R> {
    r: R,
}

impl<R> Converse<R> {
    fn _new(r: R) -> Self {
        Self { r }
    }
}

impl<R> Relation for Converse<R>
where
    R: Relation,
{
    type Domain = R::Domain;
    fn call(&self, x: &Self::Domain, y: &Self::Domain) -> bool {
        self.r.call(y, x)
    }
}

impl<R> Procedure for (Converse<R>, Z0)
where
    R: Relation,
{
    type InputType = R::Domain;
}

#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct ComplementOfConverse<R> {
    r: R,
}

impl<R> ComplementOfConverse<R> {
    pub fn new(r: R) -> Self {
        Self { r }
    }
}

impl<R> Relation for ComplementOfConverse<R>
where
    R: Relation,
{
    type Domain = R::Domain;
    fn call(&self, a: &Self::Domain, b: &Self::Domain) -> bool {
        !self.r.call(b, a)
    }
}

impl<R> Procedure for (ComplementOfConverse<R>, Z0)
where
    R: Relation,
{
    type InputType = R::Domain;
}

#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct SymmetricComplement<R> {
    r: R,
}

impl<R> SymmetricComplement<R> {
    fn _new(r: R) -> Self {
        SymmetricComplement { r }
    }
}

impl<R> Relation for SymmetricComplement<R>
where
    R: Relation,
{
    type Domain = R::Domain;
    fn call(&self, a: &Self::Domain, b: &Self::Domain) -> bool {
        !self.r.call(a, b) && !self.r.call(b, a)
    }
}

impl<R> Procedure for (SymmetricComplement<R>, Z0)
where
    R: Relation,
{
    type InputType = R::Domain;
}

pub fn select_0_2<'a, R>(a: &'a R::Domain, b: &'a R::Domain, r: &R) -> &'a R::Domain
where
    R: Relation,
{
    // Precondition: $\func{weak\_ordering}(r)$
    if r.call(b, a) {
        return b;
    }
    a
}

pub fn select_1_2<'a, R>(a: &'a R::Domain, b: &'a R::Domain, r: &R) -> &'a R::Domain
where
    R: Relation,
{
    // Precondition: $\func{weak\_ordering}(r)$
    if r.call(b, a) {
        return a;
    }
    b
}

pub fn select_0_3<'a, R>(
    a: &'a R::Domain,
    b: &'a R::Domain,
    c: &'a R::Domain,
    r: &R,
) -> &'a R::Domain
where
    R: Relation,
{
    select_0_2(select_0_2(a, b, r), c, r)
}

pub fn select_2_3<'a, R>(
    a: &'a R::Domain,
    b: &'a R::Domain,
    c: &'a R::Domain,
    r: &R,
) -> &'a R::Domain
where
    R: Relation,
{
    select_1_2(select_1_2(a, b, r), c, r)
}

pub fn select_1_3_ab<'a, R>(
    a: &'a R::Domain,
    b: &'a R::Domain,
    c: &'a R::Domain,
    r: &R,
) -> &'a R::Domain
where
    R: Relation,
{
    if !r.call(c, b) {
        return b;
    } // $a$, $b$, $c$ are sorted
    select_1_2(a, c, r) // $b$ is not the median
}

pub fn select_1_3<'a, R>(
    a: &'a R::Domain,
    b: &'a R::Domain,
    c: &'a R::Domain,
    r: &R,
) -> &'a R::Domain
where
    R: Relation,
{
    if r.call(b, a) {
        return select_1_3_ab(b, a, c, r);
    }
    select_1_3_ab(a, b, c, r)
}

pub fn select_1_4_ab_cd<'a, R>(
    a: &'a R::Domain,
    b: &'a R::Domain,
    c: &'a R::Domain,
    d: &'a R::Domain,
    r: &R,
) -> &'a R::Domain
where
    R: Relation,
{
    if r.call(c, a) {
        return select_0_2(a, d, r);
    }
    select_0_2(b, c, r)
}

pub fn select_1_4_ab<'a, R>(
    a: &'a R::Domain,
    b: &'a R::Domain,
    c: &'a R::Domain,
    d: &'a R::Domain,
    r: &R,
) -> &'a R::Domain
where
    R: Relation,
{
    if r.call(d, c) {
        return select_1_4_ab_cd(a, b, d, c, r);
    }
    select_1_4_ab_cd(a, b, c, d, r)
}

pub fn select_1_4<'a, R>(
    a: &'a R::Domain,
    b: &'a R::Domain,
    c: &'a R::Domain,
    d: &'a R::Domain,
    r: &R,
) -> &'a R::Domain
where
    R: Relation,
{
    if r.call(b, a) {
        return select_1_4_ab(b, a, c, d, r);
    }
    select_1_4_ab(a, b, c, d, r)
}

// Exercise 4.4: select_2_4

// Order selection procedures with stability indices

pub trait CompareStrictOrReflexive<R>
where
    R: Relation,
{
    fn call(a: &R::Domain, b: &R::Domain, r: &R) -> bool;
}

impl<R> CompareStrictOrReflexive<R> for True
where
    R: Relation, // strict
{
    fn call(a: &R::Domain, b: &R::Domain, r: &R) -> bool {
        r.call(a, b)
    }
}

impl<R> CompareStrictOrReflexive<R> for False
where
    R: Relation, // reflexive
{
    fn call(a: &R::Domain, b: &R::Domain, r: &R) -> bool {
        !r.call(b, a) // $\func{complement\_of\_converse}_r(a, b)$
    }
}

pub fn select_0_2_1<'a, IA, IB, R>(a: &'a R::Domain, b: &'a R::Domain, r: &R) -> &'a R::Domain
where
    R: Relation,
    IA: Cmp<IB> + IsLessPrivate<IB, Compare<IA, IB>>,
    <IA as IsLess<IB>>::Output: CompareStrictOrReflexive<R>,
{
    if <op!(IA < IB)>::call(b, a, r) {
        return b;
    }
    a
}

pub fn select_1_2_1<'a, IA, IB, R>(a: &'a R::Domain, b: &'a R::Domain, r: &R) -> &'a R::Domain
where
    R: Relation,
    IA: Cmp<IB> + IsLessPrivate<IB, Compare<IA, IB>>,
    <IA as IsLess<IB>>::Output: CompareStrictOrReflexive<R>,
{
    if <op!(IA < IB)>::call(b, a, r) {
        return a;
    }
    b
}

pub fn select_1_4_ab_cd_1<'a, IA, IB, IC, ID, R>(
    a: &'a R::Domain,
    b: &'a R::Domain,
    c: &'a R::Domain,
    d: &'a R::Domain,
    r: &R,
) -> &'a R::Domain
where
    R: Relation,
    IA: Cmp<IC> + IsLessPrivate<IC, Compare<IA, IC>> + Cmp<ID> + IsLessPrivate<ID, Compare<IA, ID>>,
    <IA as IsLess<IC>>::Output: CompareStrictOrReflexive<R>,
    <IA as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
    IB: Cmp<IC> + IsLessPrivate<IC, Compare<IB, IC>>,
    <IB as IsLess<IC>>::Output: CompareStrictOrReflexive<R>,
{
    if <op!(IA < IC)>::call(c, a, r) {
        return select_0_2_1::<IA, ID, R>(a, d, r);
    }
    select_0_2_1::<IB, IC, R>(b, c, r)
}

pub fn select_1_4_ab_1<'a, IA, IB, IC, ID, R>(
    a: &'a R::Domain,
    b: &'a R::Domain,
    c: &'a R::Domain,
    d: &'a R::Domain,
    r: &R,
) -> &'a R::Domain
where
    R: Relation,
    IA: Cmp<IC> + IsLessPrivate<IC, Compare<IA, IC>>,
    <IA as IsLess<IC>>::Output: CompareStrictOrReflexive<R>,
    IA: Cmp<ID> + IsLessPrivate<ID, Compare<IA, ID>>,
    <IA as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
    IB: Cmp<IC> + IsLessPrivate<IC, Compare<IB, IC>>,
    <IB as IsLess<IC>>::Output: CompareStrictOrReflexive<R>,
    IB: Cmp<ID> + IsLessPrivate<ID, Compare<IB, ID>>,
    <IB as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
    IC: Cmp<ID> + IsLessPrivate<ID, Compare<IC, ID>>,
    <IC as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
{
    if <op!(IC < ID)>::call(d, c, r) {
        return select_1_4_ab_cd_1::<IA, IB, ID, IC, R>(a, b, d, c, r);
    }
    select_1_4_ab_cd_1::<IA, IB, IC, ID, R>(a, b, c, d, r)
}

pub fn select_1_4_1<'a, IA, IB, IC, ID, R>(
    a: &'a R::Domain,
    b: &'a R::Domain,
    c: &'a R::Domain,
    d: &'a R::Domain,
    r: &R,
) -> &'a R::Domain
where
    R: Relation,
    IA: Cmp<IB> + IsLessPrivate<IB, Compare<IA, IB>>,
    <IA as IsLess<IB>>::Output: CompareStrictOrReflexive<R>,
    IA: Cmp<IC> + IsLessPrivate<IC, Compare<IA, IC>>,
    <IA as IsLess<IC>>::Output: CompareStrictOrReflexive<R>,
    IA: Cmp<ID> + IsLessPrivate<ID, Compare<IA, ID>>,
    <IA as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
    IB: Cmp<IC> + IsLessPrivate<IC, Compare<IB, IC>>,
    <IB as IsLess<IC>>::Output: CompareStrictOrReflexive<R>,
    IB: Cmp<ID> + IsLessPrivate<ID, Compare<IB, ID>>,
    <IB as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
    IC: Cmp<ID> + IsLessPrivate<ID, Compare<IC, ID>>,
    <IC as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
{
    if <op!(IA < IB)>::call(b, a, r) {
        return select_1_4_ab_1::<IB, IA, IC, ID, R>(b, a, c, d, r);
    }
    select_1_4_ab_1::<IA, IB, IC, ID, R>(a, b, c, d, r)
}

pub fn select_2_5_ab_cd<'a, IA, IB, IC, ID, IE, R>(
    a: &'a R::Domain,
    b: &'a R::Domain,
    c: &'a R::Domain,
    d: &'a R::Domain,
    e: &'a R::Domain,
    r: &R,
) -> &'a R::Domain
where
    R: Relation,
    IA: Cmp<IC> + IsLessPrivate<IC, Compare<IA, IC>>,
    <IA as IsLess<IC>>::Output: CompareStrictOrReflexive<R>,
    IA: Cmp<ID> + IsLessPrivate<ID, Compare<IA, ID>>,
    <IA as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
    IA: Cmp<IE> + IsLessPrivate<IE, Compare<IA, IE>>,
    <IA as IsLess<IE>>::Output: CompareStrictOrReflexive<R>,
    IB: Cmp<ID> + IsLessPrivate<ID, Compare<IB, ID>>,
    <IB as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
    IB: Cmp<IE> + IsLessPrivate<IE, Compare<IB, IE>>,
    <IB as IsLess<IE>>::Output: CompareStrictOrReflexive<R>,
    IC: Cmp<IB> + IsLessPrivate<IB, Compare<IC, IB>>,
    <IC as IsLess<IB>>::Output: CompareStrictOrReflexive<R>,
    IC: Cmp<IE> + IsLessPrivate<IE, Compare<IC, IE>>,
    <IC as IsLess<IE>>::Output: CompareStrictOrReflexive<R>,
    ID: Cmp<IB> + IsLessPrivate<IB, Compare<ID, IB>>,
    <ID as IsLess<IB>>::Output: CompareStrictOrReflexive<R>,
    ID: Cmp<IE> + IsLessPrivate<IE, Compare<ID, IE>>,
    <ID as IsLess<IE>>::Output: CompareStrictOrReflexive<R>,
{
    if <op!(IA < IC)>::call(c, a, r) {
        return select_1_4_ab_1::<IA, IB, ID, IE, R>(a, b, d, e, r);
    }
    select_1_4_ab_1::<IC, ID, IB, IE, R>(c, d, b, e, r)
}

pub fn select_2_5_ab<'a, IA, IB, IC, ID, IE, R>(
    a: &'a R::Domain,
    b: &'a R::Domain,
    c: &'a R::Domain,
    d: &'a R::Domain,
    e: &'a R::Domain,
    r: &R,
) -> &'a R::Domain
where
    R: Relation,
    IA: Cmp<IC> + IsLessPrivate<IC, Compare<IA, IC>>,
    <IA as IsLess<IC>>::Output: CompareStrictOrReflexive<R>,
    IA: Cmp<ID> + IsLessPrivate<ID, Compare<IA, ID>>,
    <IA as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
    IA: Cmp<IE> + IsLessPrivate<IE, Compare<IA, IE>>,
    <IA as IsLess<IE>>::Output: CompareStrictOrReflexive<R>,
    IB: Cmp<IC> + IsLessPrivate<IC, Compare<IB, IC>>,
    <IB as IsLess<IC>>::Output: CompareStrictOrReflexive<R>,
    IB: Cmp<ID> + IsLessPrivate<ID, Compare<IB, ID>>,
    <IB as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
    IB: Cmp<IE> + IsLessPrivate<IE, Compare<IB, IE>>,
    <IB as IsLess<IE>>::Output: CompareStrictOrReflexive<R>,
    IC: Cmp<IB> + IsLessPrivate<IB, Compare<IC, IB>>,
    <IC as IsLess<IB>>::Output: CompareStrictOrReflexive<R>,
    IC: Cmp<ID> + IsLessPrivate<ID, Compare<IC, ID>>,
    <IC as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
    IC: Cmp<IE> + IsLessPrivate<IE, Compare<IC, IE>>,
    <IC as IsLess<IE>>::Output: CompareStrictOrReflexive<R>,
    ID: Cmp<IB> + IsLessPrivate<IB, Compare<ID, IB>>,
    <ID as IsLess<IB>>::Output: CompareStrictOrReflexive<R>,
    ID: Cmp<IE> + IsLessPrivate<IE, Compare<ID, IE>>,
    <ID as IsLess<IE>>::Output: CompareStrictOrReflexive<R>,
{
    if <op!(IC < ID)>::call(d, c, r) {
        return select_2_5_ab_cd::<IA, IB, ID, IC, IE, R>(a, b, d, c, e, r);
    }
    select_2_5_ab_cd::<IA, IB, IC, ID, IE, R>(a, b, c, d, e, r)
}

pub fn select_2_5<'a, IA, IB, IC, ID, IE, R>(
    a: &'a R::Domain,
    b: &'a R::Domain,
    c: &'a R::Domain,
    d: &'a R::Domain,
    e: &'a R::Domain,
    r: &R,
) -> &'a R::Domain
where
    R: Relation,
    IA: Cmp<IB> + IsLessPrivate<IB, Compare<IA, IB>>,
    <IA as IsLess<IB>>::Output: CompareStrictOrReflexive<R>,
    IA: Cmp<IC> + IsLessPrivate<IC, Compare<IA, IC>>,
    <IA as IsLess<IC>>::Output: CompareStrictOrReflexive<R>,
    IA: Cmp<ID> + IsLessPrivate<ID, Compare<IA, ID>>,
    <IA as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
    IA: Cmp<IE> + IsLessPrivate<IE, Compare<IA, IE>>,
    <IA as IsLess<IE>>::Output: CompareStrictOrReflexive<R>,
    IB: Cmp<IC> + IsLessPrivate<IC, Compare<IB, IC>>,
    <IB as IsLess<IC>>::Output: CompareStrictOrReflexive<R>,
    IB: Cmp<ID> + IsLessPrivate<ID, Compare<IB, ID>>,
    <IB as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
    IB: Cmp<IE> + IsLessPrivate<IE, Compare<IB, IE>>,
    <IB as IsLess<IE>>::Output: CompareStrictOrReflexive<R>,
    IC: Cmp<IA> + IsLessPrivate<IA, Compare<IC, IA>>,
    <IC as IsLess<IA>>::Output: CompareStrictOrReflexive<R>,
    IC: Cmp<IB> + IsLessPrivate<IB, Compare<IC, IB>>,
    <IC as IsLess<IB>>::Output: CompareStrictOrReflexive<R>,
    IC: Cmp<ID> + IsLessPrivate<ID, Compare<IC, ID>>,
    <IC as IsLess<ID>>::Output: CompareStrictOrReflexive<R>,
    IC: Cmp<IE> + IsLessPrivate<IE, Compare<IC, IE>>,
    <IC as IsLess<IE>>::Output: CompareStrictOrReflexive<R>,
    ID: Cmp<IA> + IsLessPrivate<IA, Compare<ID, IA>>,
    <ID as IsLess<IA>>::Output: CompareStrictOrReflexive<R>,
    ID: Cmp<IB> + IsLessPrivate<IB, Compare<ID, IB>>,
    <ID as IsLess<IB>>::Output: CompareStrictOrReflexive<R>,
    ID: Cmp<IE> + IsLessPrivate<IE, Compare<ID, IE>>,
    <ID as IsLess<IE>>::Output: CompareStrictOrReflexive<R>,
{
    if <op!(IA < IB)>::call(b, a, r) {
        return select_2_5_ab::<IB, IA, IC, ID, IE, R>(b, a, c, d, e, r);
    }
    select_2_5_ab::<IA, IB, IC, ID, IE, R>(a, b, c, d, e, r)
}

// Exercise 4.5. Find an algorithm for median of 5 that does slightly fewer comparisons
// on average

pub fn median_5<'a, R>(
    a: &'a R::Domain,
    b: &'a R::Domain,
    c: &'a R::Domain,
    d: &'a R::Domain,
    e: &'a R::Domain,
    r: &R,
) -> &'a R::Domain
where
    R: Relation,
{
    select_2_5::<Z0, P1, P2, P3, P4, R>(a, b, c, d, e, r)
}

// Exercise 4.6. Prove the stability of every order selection procedure in this section
// Exercise 4.7. Verify the correctness and stability of every order selection procedure
// in this section by exhaustive testing

// Natural total ordering

#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct Less<T>(PhantomData<T>);

impl<T> Relation for Less<T>
where
    T: Regular + TotallyOrdered,
{
    type Domain = T;
    fn call(&self, x: &T, y: &T) -> bool {
        x < y
    }
}

impl<T> Procedure for (Less<T>, Z0)
where
    T: TotallyOrdered,
{
    type InputType = T;
}

pub fn min<'a, T>(a: &'a T, b: &'a T) -> &'a T
where
    T: Regular + TotallyOrdered,
{
    select_0_2(a, b, &Less::<T>::default())
}

pub fn max<'a, T>(a: &'a T, b: &'a T) -> &'a T
where
    T: Regular + TotallyOrdered,
{
    select_1_2(a, b, &Less::<T>::default())
}

/*
// Clusters of related procedures: equality and ordering

template<typename T>
    requires(Regular(T))
bool operator!=(const T& x, const T& y)
{
    return !(x==y);
}

template<typename T>
    requires(TotallyOrdered(T))
bool operator>(const T& x, const T& y)
{
    return y < x;
}

template<typename T>
    requires(TotallyOrdered(T))
bool operator<=(const T& x, const T& y)
{
    return !(y < x);
}

template<typename T>
    requires(TotallyOrdered(T))
bool operator>=(const T& x, const T& y)
{
    return !(x < y);
}


// Exercise 4.8: Rewrite the algorithms in this chapter using three-valued comparison
*/

//
//  Chapter 5. Ordered algebraic structures
//

pub trait AdditiveSemigroup: Regular {
    fn add(&self, x: &Self) -> Self;
}

#[derive(Clone, Default, Eq, PartialEq)]
pub struct Plus<T>(PhantomData<T>);

impl<T> BinaryOperation for Plus<T>
where
    T: AdditiveSemigroup,
{
    type Domain = T;
    fn call(&self, x: &T, y: &T) -> T {
        x.add(y)
    }
}

impl<T> Procedure for (Plus<T>, Z0)
where
    T: AdditiveSemigroup,
{
    type InputType = T;
}

pub trait MultiplicativeSemigroup: Regular {
    fn mul(&self, y: &Self) -> Self;
}

#[derive(Clone, Default, Eq, PartialEq)]
pub struct Multiplies<T>(PhantomData<T>);

impl<T> BinaryOperation for Multiplies<T>
where
    T: MultiplicativeSemigroup,
{
    type Domain = T;
    fn call(&self, x: &T, y: &T) -> T {
        x.mul(y)
    }
}

impl<T> Procedure for (Multiplies<T>, Z0) {
    type InputType = T;
}

pub trait SemigroupOperation: BinaryOperation {}
impl<T> SemigroupOperation for T where T: BinaryOperation {}

pub struct MultipliesTransformation<Op>
where
    Op: SemigroupOperation,
{
    x: Op::Domain,
    op: Op,
}

impl<Op> MultipliesTransformation<Op>
where
    Op: SemigroupOperation,
{
    pub fn new(x: Op::Domain, op: Op) -> Self {
        Self { x, op }
    }
    pub fn call(&self, y: &Op::Domain) -> Op::Domain {
        self.op.call(&self.x, y)
    }
}

impl<Op> Procedure for (MultipliesTransformation<Op>, Z0)
where
    Op: SemigroupOperation,
{
    type InputType = Op::Domain;
}

pub trait AdditiveMonoid: AdditiveSemigroup {
    fn zero() -> Self;
}

pub trait AdditiveGroup: AdditiveMonoid {
    fn neg(&self) -> Self;
}

pub struct Negate<T>(PhantomData<T>);

impl<T> Negate<T> {
    pub fn call(x: &T) -> T
    where
        T: AdditiveGroup,
    {
        x.neg()
    }
}

impl<T> Procedure for (Negate<T>, Z0) {
    type InputType = T;
}

pub trait OrderedAdditiveGroup: OrderedAdditiveMonoid + AdditiveGroup {}

pub fn abs<T>(a: T) -> T
where
    T: OrderedAdditiveGroup,
{
    if a < T::zero() {
        a.neg()
    } else {
        a
    }
}

pub trait OrderedAdditiveSemigroup: AdditiveSemigroup + TotallyOrdered {}

pub trait OrderedAdditiveMonoid: AdditiveMonoid + OrderedAdditiveSemigroup {}

pub trait CancellableMonoid: OrderedAdditiveMonoid {
    fn sub(&self, x: &Self) -> Self;
}

pub fn slow_remainder<T>(mut a: T, b: &T) -> T
where
    T: CancellableMonoid,
{
    // Precondition: $a \geq 0 \wedge b > 0$
    while *b <= a {
        a = a.sub(b);
    }
    a
}

pub trait ArchimedeanMonoid: CancellableMonoid {
    type QuotientType: Integer;
}

pub fn slow_quotient<T>(mut a: T, b: &T) -> T::QuotientType
where
    T: ArchimedeanMonoid,
{
    // Precondition: $a \geq 0 \wedge b > 0$
    let mut n = T::QuotientType::zero();
    while *b <= a {
        a = a.sub(b);
        n = successor(n);
    }
    n
}

pub fn remainder_recursive<T>(mut a: T, b: &T) -> T
where
    T: ArchimedeanMonoid,
{
    // Precondition: $a \geq b > 0$
    if a.sub(b) >= *b {
        a = remainder_recursive(a, &b.add(b));
        if a < *b {
            return a;
        }
    }
    a.sub(b)
}

pub fn remainder_nonnegative<T>(a: T, b: &T) -> T
where
    T: ArchimedeanMonoid,
{
    // Precondition: $a \geq 0 \wedge b > 0$
    if a < *b {
        return a;
    }
    remainder_recursive(a, b)
}

/* The next function is due to:
    Robert W. Floyd and Donald E. Knuth.
    Addition machines.
    \emph{SIAM Journal on Computing},
    Volume 19, Number 2, 1990, pages 329--340.
*/

pub fn remainder_nonnegative_fibonacci<T>(mut a: T, mut b: T) -> T
where
    T: ArchimedeanMonoid,
{
    // Precondition: $a \geq 0 \wedge b > 0$
    if a < b {
        return a;
    }
    let mut c = b.clone();
    loop {
        let tmp = c.clone();
        c = b.add(&c);
        b = tmp;
        if a < c {
            break;
        }
    }
    loop {
        if a >= b {
            a = a.sub(&b);
        }
        let tmp = c.sub(&b);
        c = b;
        b = tmp;
        if b >= c {
            break;
        }
    }
    a
}

pub fn largest_doubling<T>(a: &T, mut b: T) -> T
where
    T: ArchimedeanMonoid,
{
    // Precondition: $a \geq b > 0$
    while b <= a.sub(&b) {
        b = b.add(&b)
    }
    b
}

pub trait HalvableMonoid: ArchimedeanMonoid {
    fn half(&self) -> Self;
}

pub fn remainder_nonnegative_iterative<T>(mut a: T, b: &T) -> T
where
    T: HalvableMonoid,
{
    // Precondition: $a \geq 0 \wedge b > 0$
    if a < *b {
        return a;
    }
    let mut c = largest_doubling(&a, b.clone());
    a = a.sub(&c);
    while c != *b {
        c = c.half();
        if c <= a {
            a = a.sub(&c);
        }
    }
    a
}

// Jon Brandt suggested this algorithm (it is not mentioned in chapter 5):

pub fn remainder_nonnegative_with_largest_doubling<T>(mut a: T, b: &T) -> T
where
    T: ArchimedeanMonoid,
{
    // Precondition: $a \geq T(0) \wedge b > T(0)$
    while *b <= a {
        a = a.sub(&largest_doubling(&a, b.clone()));
    }
    a
}

pub fn subtractive_gcd_nonzero<T>(mut a: T, mut b: T) -> T
where
    T: ArchimedeanMonoid,
{
    // Precondition: $a > 0 \wedge b > 0$
    loop {
        match b.cmp(&a) {
            std::cmp::Ordering::Less => a = a.sub(&b),
            std::cmp::Ordering::Greater => b = b.sub(&a),
            std::cmp::Ordering::Equal => return a,
        }
    }
}

pub trait EuclideanMonoid: ArchimedeanMonoid {}

pub fn subtractive_gcd<T>(mut a: T, mut b: T) -> T
where
    T: EuclideanMonoid,
{
    // Precondition: $a \geq 0 \wedge b \geq 0 \wedge \neg(a = 0 \wedge b = 0)$
    loop {
        if b == T::zero() {
            return a;
        }
        while b <= a {
            a = a.sub(&b);
        }
        if a == T::zero() {
            return b;
        }
        while a <= b {
            b = b.sub(&a);
        }
    }
}

pub fn fast_subtractive_gcd<T>(mut a: T, mut b: T) -> T
where
    T: EuclideanMonoid,
{
    // Precondition: $a \geq 0 \wedge b \geq 0 \wedge \neg(a = 0 \wedge b = 0)$
    loop {
        if b == T::zero() {
            return a;
        }
        a = remainder_nonnegative(a, &b);
        if a == T::zero() {
            return b;
        }
        b = remainder_nonnegative(b, &a);
    }
}

pub trait MultiplicativeMonoid: MultiplicativeSemigroup {}

pub trait Semiring: AdditiveMonoid + MultiplicativeMonoid {}

pub trait CommutativeSemiring: Semiring {}

pub trait EuclideanSemiring: CommutativeSemiring {
    fn remainder(&self, x: &Self) -> Self;
}

pub fn gcd<T>(mut a: T, mut b: T) -> T
where
    T: EuclideanSemiring,
{
    // Precondition: $\neg(a = 0 \wedge b = 0)$
    loop {
        if b == T::zero() {
            return a;
        }
        a = a.remainder(&b);
        if a == T::zero() {
            return b;
        }
        b = b.remainder(&a);
    }
}

pub trait Semimodule: AdditiveMonoid {}

pub trait EuclideanSemimodule: Semimodule {
    fn remainder(&self, x: &Self) -> Self;
}

pub fn gcd_1<T>(mut a: T, mut b: T) -> T
where
    T: EuclideanSemimodule,
{
    // Precondition: $\neg(a = 0 \wedge b = 0)$
    loop {
        if b == T::zero() {
            return a;
        }
        a = a.remainder(&b);
        if a == T::zero() {
            return b;
        }
        b = b.remainder(&a);
    }
}

// Exercise 5.3:

pub fn stein_gcd_nonnegative<T>(mut a: T, mut b: T) -> T
where
    T: Integer,
{
    // Precondition: $a \geq 0 \wedge b \geq 0 \wedge \neg(a = 0 \wedge b = 0)$
    if zero(&a) {
        return b;
    }
    if zero(&b) {
        return a;
    }
    let mut d = T::zero();
    while even(a.clone()) && even(b.clone()) {
        a = half_nonnegative(a);
        b = half_nonnegative(b);
        d = d + T::one();
    }
    while even(a.clone()) {
        a = half_nonnegative(a);
    }
    while even(b.clone()) {
        b = half_nonnegative(b);
    }
    loop {
        match a.cmp(&b) {
            std::cmp::Ordering::Less => {
                b = b - a.clone();
                loop {
                    b = half_nonnegative(b);
                    if odd(b.clone()) {
                        break;
                    }
                }
            }
            std::cmp::Ordering::Greater => {
                a = a - b.clone();
                loop {
                    a = half_nonnegative(a);
                    if odd(a.clone()) {
                        break;
                    }
                }
            }
            std::cmp::Ordering::Equal => {
                return binary_scale_up_nonnegative(a, d);
            }
        }
    }
}

pub fn quotient_remainder_nonnegative<T>(mut a: T, b: &T) -> Pair<T::QuotientType, T>
where
    T: ArchimedeanMonoid,
{
    // Precondition: $a \geq 0 \wedge b > 0$
    if a < *b {
        return Pair::new(T::QuotientType::zero(), a);
    }
    if a.sub(b) < *b {
        return Pair::new(T::QuotientType::one(), a.sub(&b));
    }
    let q = quotient_remainder_nonnegative(a, &b.add(&b));
    let m = twice(q.m0);
    a = q.m1;
    if a < *b {
        Pair::new(m, a)
    } else {
        Pair::new(successor(m), a.sub(&b))
    }
}

pub fn quotient_remainder_nonnegative_iterative<T>(mut a: T, b: &T) -> Pair<T::QuotientType, T>
where
    T: HalvableMonoid,
{
    // Precondition: $a \geq 0 \wedge b > 0$
    if a < *b {
        return Pair::new(T::QuotientType::zero(), a);
    }
    let mut c = largest_doubling(&a, b.clone());
    a = a.sub(&c);
    let mut n = T::QuotientType::one();
    while c != *b {
        n = twice(n);
        c = c.half();
        if c <= a {
            a = a.sub(&c);
            n = successor(n);
        }
    }
    Pair::new(n, a)
}

pub trait ArchimedeanGroup: ArchimedeanMonoid + AdditiveGroup {}

pub fn remainder<Op>(a: &Op::Domain, b: &Op::Domain, rem: &Op) -> Op::Domain
where
    Op: BinaryOperation,
    Op::Domain: ArchimedeanGroup,
{
    // Precondition: $b \neq 0$
    let mut r;
    if *a < Op::Domain::zero() {
        if *b < Op::Domain::zero() {
            r = rem.call(&a.neg(), &b.neg()).neg();
        } else {
            r = rem.call(&a.neg(), &b);
            if r != Op::Domain::zero() {
                r = b.sub(&r);
            }
        }
    } else if *b < Op::Domain::zero() {
        r = rem.call(&a, &b.neg());
        if r != Op::Domain::zero() {
            r = b.add(&r);
        }
    } else {
        r = rem.call(&a, &b);
    }
    r
}

pub trait HomogeneousFunction {
    type Domain: ArchimedeanGroup;
    fn call(
        &self,
        a: &Self::Domain,
        b: &Self::Domain,
    ) -> Pair<<Self::Domain as ArchimedeanMonoid>::QuotientType, Self::Domain>;
}

pub fn quotient_remainder<F>(
    a: &F::Domain,
    b: &F::Domain,
    quo_rem: &F,
) -> Pair<<F::Domain as ArchimedeanMonoid>::QuotientType, F::Domain>
where
    F: HomogeneousFunction,
    <F::Domain as ArchimedeanMonoid>::QuotientType: AdditiveGroup,
{
    // Precondition: $b \neq 0$
    let mut q_r;
    if *a < F::Domain::zero() {
        if *b < F::Domain::zero() {
            q_r = quo_rem.call(&a.neg(), &b.neg());
            q_r.m1 = q_r.m1.neg();
        } else {
            q_r = quo_rem.call(&a.neg(), &b);
            if q_r.m1 != F::Domain::zero() {
                q_r.m1 = b.sub(&q_r.m1);
                q_r.m0 = successor(q_r.m0);
            }
            q_r.m0 = q_r.m0.neg();
        }
    } else if *b < F::Domain::zero() {
        q_r = quo_rem.call(&a, &b.neg());
        if q_r.m1 != AdditiveMonoid::zero() {
            q_r.m1 = b.add(&q_r.m1);
            q_r.m0 = successor(q_r.m0);
        }
        q_r.m0 = q_r.m0.neg();
    } else {
        q_r = quo_rem.call(a, b);
    }
    q_r
}

//
//  Chapter 6. Iterators
//

pub trait Iterator: Regular {
    type DistanceType: Integer;
    fn successor(&self) -> Self;
    fn add(mut self, mut n: Self::DistanceType) -> Self
    where
        Self: Sized,
    {
        // Precondition: $n \geq 0 \wedge \property{weak\_range}(f, n)$
        while !zero(&n) {
            n = predecessor(n);
            self = self.successor();
        }
        self
    }
    fn sub(mut self, f: &Self) -> Self::DistanceType {
        // Precondition: $\property{bounded\_range}(f, l)$
        let mut n = Self::DistanceType::zero();
        while self != *f {
            n = successor(n);
            self = self.successor();
        }
        n
    }
}

pub fn increment<I>(x: &mut I)
where
    I: Iterator,
{
    // Precondition: $\func{successor}(x)$ is defined
    *x = x.successor();
}

pub trait Reference {
    type ValueType: Regular;
}

pub trait Readable: Reference + Regular {
    fn source(&self) -> &Self::ValueType;
}

pub fn for_each<I, Proc>(mut f: I, l: &I, mut proc: Proc) -> Proc
where
    I: Readable + Iterator,
    Proc: FnMut(&I::ValueType),
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while f != *l {
        proc(f.source());
        f = f.successor();
    }
    proc
}

pub fn find<I>(mut f: I, l: &I, x: &I::ValueType) -> I
where
    I: Readable + Iterator,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while f != *l && f.source() != x {
        f = f.successor();
    }
    f
}

pub fn find_not<I>(mut f: I, l: &I, x: &I::ValueType) -> I
where
    I: Readable + Iterator,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while f != *l && f.source() == x {
        f = f.successor();
    }
    f
}

pub fn find_if<I, P>(mut f: I, l: &I, p: &P) -> I
where
    I: Readable + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while f != *l && !p.call(f.source()) {
        f = f.successor();
    }
    f
}

pub fn find_if_not<I, P>(mut f: I, l: &I, p: &P) -> I
where
    I: Readable + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while f != *l && p.call(f.source()) {
        f = f.successor();
    }
    f
}

// Exercise 6.1: quantifier functions

pub fn all<I, P>(f: I, l: &I, p: &P) -> bool
where
    I: Readable + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    *l == find_if_not(f, l, p)
}

pub fn none<I, P>(f: I, l: &I, p: &P) -> bool
where
    I: Readable + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    *l == find_if(f, l, p)
}

pub fn not_all<I, P>(f: I, l: &I, p: &P) -> bool
where
    I: Readable + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    !all(f, l, p)
}

pub fn some<I, P>(f: I, l: &I, p: &P) -> bool
where
    I: Readable + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    !none(f, l, p)
}

pub fn count_if<I, P, J>(mut f: I, l: &I, p: &P, mut j: J) -> J
where
    I: Readable + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
    J: Iterator,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while f != *l {
        if p.call(f.source()) {
            j = j.successor();
        }
        f = f.successor();
    }
    j
}

// Exercise 6.2: implement count_if using for_each

pub fn count_if_1<I, P>(f: I, l: &I, p: &P) -> I::DistanceType
where
    I: Readable + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
    I::DistanceType: Iterator,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    count_if(f, l, p, I::DistanceType::zero())
}

pub fn count<I, J>(mut f: I, l: &I, x: &I::ValueType, mut j: J) -> J
where
    I: Readable + Iterator,
    J: Iterator,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while f != *l {
        if f.source() == x {
            j = j.successor();
        }
        f = f.successor();
    }
    j
}

pub fn count_1<I>(f: I, l: &I, x: &I::ValueType) -> I::DistanceType
where
    I: Readable + Iterator,
    I::DistanceType: Iterator,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    count(f, l, x, I::DistanceType::zero())
}

pub fn count_not<I, J>(mut f: I, l: &I, x: &I::ValueType, mut j: J) -> J
where
    I: Readable + Iterator,
    J: Iterator,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while f != *l {
        if f.source() != x {
            j = j.successor();
        }
        f = f.successor();
    }
    j
}

pub fn count_not_1<I>(f: I, l: &I, x: &I::ValueType) -> I::DistanceType
where
    I: Readable + Iterator,
    I::DistanceType: Iterator,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    count_not(f, l, x, I::DistanceType::zero())
}

pub fn count_if_not<I, P, J>(mut f: I, l: &I, p: &P, mut j: J) -> J
where
    I: Readable + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
    J: Iterator,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    while f != *l {
        if !p.call(f.source()) {
            j = j.successor();
        }
        f = f.successor();
    }
    j
}

pub fn count_if_not_1<I, P>(f: I, l: &I, p: &P) -> I::DistanceType
where
    I: Readable + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
    I::DistanceType: Iterator,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    count_if_not(f, l, p, I::DistanceType::zero())
}

pub fn reduce_nonempty<I, Op, F>(mut f: I, l: &I, op: &Op, fun: &F) -> Op::Domain
where
    I: Iterator,
    Op: BinaryOperation,
    F: Fn(&I) -> &Op::Domain,
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge f \neq l$
    // Precondition: $\property{partially\_associative}(op)$
    // Precondition: $(\forall x \in [f, l))\,fun(x)$ is defined
    let mut r = fun(&f).clone();
    f = f.successor();
    while f != *l {
        r = op.call(&r, fun(&f));
        f = f.successor();
    }
    r
}

pub fn reduce_nonempty_1<I, Op>(mut f: I, l: &I, op: &Op) -> Op::Domain
where
    I: Readable<ValueType = Op::Domain> + Iterator,
    Op: BinaryOperation,
{
    // Precondition: $\property{readable\_bounded\_range}(f, l) \wedge f \neq l$
    // Precondition: $\property{partially\_associative}(op)$
    let mut r = f.source().clone();
    f = f.successor();
    while f != *l {
        r = op.call(&r, f.source());
        f = f.successor();
    }
    r
}

pub fn reduce<I, Op, F>(f: I, l: &I, op: &Op, fun: &F, z: &Op::Domain) -> Op::Domain
where
    I: Iterator,
    Op: BinaryOperation,
    F: Fn(&I) -> &Op::Domain,
{
    // Precondition: $\property{bounded\_range}(f, l)$
    // Precondition: $\property{partially\_associative}(op)$
    // Precondition: $(\forall x \in [f, l))\,fun(x)$ is defined
    if f == *l {
        return z.clone();
    }
    reduce_nonempty(f, l, op, fun)
}

pub trait ReadableIterator: Readable + Iterator {}
impl<T> ReadableIterator for T where T: Readable + Iterator {}

pub fn reduce_1<I, Op>(f: I, l: &I, op: &Op, z: &Op::Domain) -> Op::Domain
where
    I: ReadableIterator,
    Op: BinaryOperation<Domain = I::ValueType>,
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    // Precondition: $\property{partially\_associative}(op)$
    if f == *l {
        return z.clone();
    }
    reduce_nonempty_1(f, l, op)
}

pub fn reduce_nonzeroes<I, Op, F>(mut f: I, l: &I, op: &Op, fun: &F, z: &Op::Domain) -> Op::Domain
where
    I: Iterator,
    Op: BinaryOperation,
    F: Fn(&I) -> &Op::Domain,
{
    // Precondition: $\property{bounded\_range}(f, l)$
    // Precondition: $\property{partially\_associative}(op)$
    // Precondition: $(\forall x \in [f, l))\,fun(x)$ is defined
    let mut x;
    loop {
        if f == *l {
            return z.clone();
        }
        x = fun(&f).clone();
        f = f.successor();
        if x != *z {
            break;
        }
    }
    while f != *l {
        let y = fun(&f).clone();
        if y != *z {
            x = op.call(&x, &y);
        }
        f = f.successor();
    }
    x
}

pub fn reduce_nonzeroes_1<I, Op>(mut f: I, l: &I, op: &Op, z: &Op::Domain) -> Op::Domain
where
    I: ReadableIterator,
    Op: BinaryOperation<Domain = I::ValueType>,
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    // Precondition: $\property{partially\_associative}(op)$
    let mut x;
    loop {
        if f == *l {
            return z.clone();
        }
        x = f.source().clone();
        f = f.successor();
        if x != *z {
            break;
        }
    }
    while f != *l {
        let y = f.source().clone();
        if y != *z {
            x = op.call(&x, &y);
        }
        f = f.successor();
    }
    x
}

pub fn reduce_2<I>(f: I, l: &I) -> I::ValueType
where
    I: Readable + Iterator,
    I::ValueType: AdditiveMonoid,
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    reduce_1(
        f,
        l,
        &Plus::<I::ValueType>::default(),
        &I::ValueType::zero(),
    )
}

pub fn for_each_n<I, Proc>(mut f: I, mut n: I::DistanceType, mut proc: Proc) -> Pair<Proc, I>
where
    I: Readable + Iterator,
    Proc: FnMut(&I::ValueType) + Regular,
{
    // Precondition: $\property{readable\_weak\_range}(f, n)$
    while !zero(&n) {
        n = predecessor(n);
        proc(f.source());
        f = f.successor();
    }
    Pair::new(proc, f)
}

pub fn find_n<I>(mut f: I, mut n: I::DistanceType, x: &I::ValueType) -> Pair<I, I::DistanceType>
where
    I: Readable + Iterator,
{
    // Precondition: $\property{readable\_weak\_range}(f, n)$
    while !zero(&n) && f.source() != x {
        n = predecessor(n);
        f = f.successor();
    }
    Pair::new(f, n)
}

// Exercise 6.3: implement variations taking a weak range instead of a bounded range
// of all the versions of find, quantifiers, count, and reduce

pub fn find_if_unguarded<I, P>(mut f: I, p: &P) -> I
where
    I: Readable + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition:
    // $(\exists l)\,\func{readable\_bounded\_range}(f, l) \wedge \func{some}(f, l, p)$
    while !p.call(f.source()) {
        f = f.successor();
    }
    f
    // Postcondition: $p(\func{source}(f))$
}

pub fn find_if_not_unguarded<I, P>(mut f: I, p: &P) -> I
where
    I: Readable + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Let $l$ be the end of the implied range starting with $f$
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{not\_all}(f, l, p)$
    while p.call(f.source()) {
        f = f.successor();
    }
    f
}

pub fn find_mismatch<I0, I1, R>(mut f0: I0, l0: &I0, mut f1: I1, l1: &I1, r: &R) -> Pair<I0, I1>
where
    I0: Readable + Iterator,
    I1: Readable<ValueType = I0::ValueType> + Iterator,
    R: Relation<Domain = I0::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f0, l0)$
    // Precondition: $\func{readable\_bounded\_range}(f1, l1)$
    while f0 != *l0 && f1 != *l1 && r.call(f0.source(), f1.source()) {
        f0 = f0.successor();
        f1 = f1.successor();
    }
    Pair::new(f0, f1)
}

pub fn find_adjacent_mismatch<I, R>(mut f: I, l: &I, r: &R) -> I
where
    I: Readable + Iterator,
    R: Relation<Domain = I::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    if f == *l {
        return f;
    }
    let mut x = f.source().clone();
    f = f.successor();
    while f != *l && r.call(&x, f.source()) {
        x = f.source().clone();
        f = f.successor();
    }
    f
}

pub fn relation_preserving<I, R>(f: I, l: &I, r: &R) -> bool
where
    I: Readable + Iterator,
    R: Relation<Domain = I::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    *l == find_adjacent_mismatch(f, l, r)
}

pub fn strictly_increasing_range<I, R>(f: I, l: &I, r: &R) -> bool
where
    I: Readable + Iterator,
    R: Relation<Domain = I::ValueType>,
{
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{weak\_ordering}(r)$
    relation_preserving(f, l, r)
}

pub fn increasing_range<I, R>(f: I, l: &I, r: &R) -> bool
where
    I: Readable + Iterator,
    R: Relation<Domain = I::ValueType>,
{
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{weak\_ordering}(r)$
    relation_preserving(f, l, &ComplementOfConverse::new(r.clone()))
}

pub fn partitioned<I, P>(f: I, l: &I, p: &P) -> bool
where
    I: Readable + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    *l == find_if_not(find_if(f, l, p), l, p)
}

// Exercise 6.6: partitioned_n

pub trait ForwardIterator: Iterator {
    fn rotate_nontrivial(self, m: Self, l: Self) -> Self
    where
        Self: Mutable,
    {
        // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
        rotate_forward_nontrivial(self, m, &l)
    }
}

impl<T> ForwardIterator for T where T: Iterator {}

pub fn find_adjacent_mismatch_forward<I, R>(mut f: I, l: &I, r: &R) -> I
where
    I: Readable + ForwardIterator,
    R: Relation<Domain = I::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    if f == *l {
        return f;
    }
    loop {
        let t = f.clone();
        f = f.successor();
        if f == *l || !r.call(t.source(), f.source()) {
            break;
        }
    }
    f
}

pub fn partition_point_n<I, P>(mut f: I, mut n: I::DistanceType, p: &P) -> I
where
    I: Readable + ForwardIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition:
    // $\func{readable\_counted\_range}(f, n) \wedge \func{partitioned\_n}(f, n, p)$
    while !zero(&n) {
        let h = half_nonnegative(n.clone());
        let m = f.clone().add(h.clone());
        if p.call(m.source()) {
            n = h;
        } else {
            n = n - successor(h);
            f = m.successor();
        }
    }
    f
}

pub fn partition_point<I, P>(f: I, l: I, p: &P) -> I
where
    I: Readable + ForwardIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{partitioned}(f, l, p)$
    let n = l.sub(&f);
    partition_point_n(f, n, p)
}

pub struct LowerBoundPredicate<'a, R>
where
    R: Relation,
{
    a: &'a R::Domain,
    r: R,
}

impl<'a, R> LowerBoundPredicate<'a, R>
where
    R: Relation,
{
    pub fn new(a: &'a R::Domain, r: R) -> Self {
        Self { a, r }
    }
}

impl<'a, R> UnaryPredicate for LowerBoundPredicate<'a, R>
where
    R: Relation,
{
    type Domain = R::Domain;
    fn call(&self, x: &Self::Domain) -> bool {
        !self.r.call(x, self.a)
    }
}

pub fn lower_bound_n<I, R>(f: I, n: I::DistanceType, a: &I::ValueType, r: &R) -> I
where
    I: Readable + ForwardIterator,
    R: Relation<Domain = I::ValueType> + Regular,
{
    // Precondition:
    // $\property{weak\_ordering(r)} \wedge \property{increasing\_counted\_range}(f, n, r)$
    let p = LowerBoundPredicate::new(a, r.clone());
    partition_point_n(f, n, &p)
}

pub struct UpperBoundPredicate<'a, R>
where
    R: Relation,
{
    a: &'a R::Domain,
    r: R,
}

impl<'a, R> UpperBoundPredicate<'a, R>
where
    R: Relation,
{
    pub fn new(a: &'a R::Domain, r: R) -> Self {
        Self { a, r }
    }
}

impl<'a, R> UnaryPredicate for UpperBoundPredicate<'a, R>
where
    R: Relation,
{
    type Domain = R::Domain;
    fn call(&self, x: &Self::Domain) -> bool {
        self.r.call(self.a, x)
    }
}

pub fn upper_bound_n<I, R>(f: I, n: I::DistanceType, a: &I::ValueType, r: &R) -> I
where
    I: Readable + ForwardIterator,
    R: Relation<Domain = I::ValueType> + Regular,
{
    // Precondition:
    // $\property{weak\_ordering(r)} \wedge \property{increasing\_counted\_range}(f, n, r)$
    let p = UpperBoundPredicate::new(a, r.clone());
    partition_point_n(f, n, &p)
}

// Exercise 6.7: equal_range

pub trait BidirectionalIterator: ForwardIterator {
    fn predecessor(&self) -> Self;
    fn rotate_nontrivial(self, m: Self, l: Self) -> Self
    where
        Self: Mutable,
    {
        // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
        rotate_bidirectional_nontrivial(self, &m, l)
    }
}

pub fn sub<I>(mut l: I, mut n: I::DistanceType) -> I
where
    I: BidirectionalIterator,
{
    // Precondition: $n \geq 0 \wedge (\exists f \in I)\,(\func{weak\_range}(f, n) \wedge l = f+n)$
    while !zero(&n) {
        n = predecessor(n);
        l = l.predecessor();
    }
    l
}

pub fn find_backward_if<I, P>(f: &I, mut l: I, p: &P) -> I
where
    I: Readable + BidirectionalIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $(f, l] \text{ is a readable bounded half-open on left range}$
    while l != *f && !p.call(l.predecessor().source()) {
        l = l.predecessor();
    }
    l
}

pub fn find_backward_if_not<I, P>(f: &I, mut l: I, p: &P) -> I
where
    I: Readable + BidirectionalIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $(f, l] \text{ is a readable bounded half-open on left range}$
    while l != *f && p.call(l.predecessor().source()) {
        l = l.predecessor();
    }
    l
}

// Exercise 6.8: optimized find_backward_if

// Exercise 6.9: palindrome predicate

pub fn find_backward_if_unguarded<I, P>(mut l: I, p: &P) -> I
where
    I: Readable + BidirectionalIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition:
    // $(\exists f \in I)\,\property{readable\_bounded\_range}(f, l) \wedge \property{some}(f, l, p)$
    loop {
        l = l.predecessor();
        if p.call(l.source()) {
            break;
        }
    }
    l
    // Postcondition: $p(\func{source}(l))$
}

pub fn find_backward_if_not_unguarded<I, P>(mut l: I, p: &P) -> I
where
    I: Readable + BidirectionalIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition:
    // $(\exists f \in I)\,\property{readable\_bounded\_range}(f, l) \wedge \property{not\_all}(f, l, p)$
    loop {
        l = l.predecessor();
        if !p.call(l.source()) {
            break;
        }
    }
    l
    // Postcondition: $\neg p(\func{source}(l))$
}

//
//  Chapter 7. Coordinate structures
//

pub trait BifurcateCoordinate: Regular {
    type WeightType: Integer;
    fn empty(&self) -> bool;
    fn has_left_successor(&self) -> bool;
    fn has_right_successor(&self) -> bool;
    fn left_successor(&self) -> Self;
    fn right_successor(&self) -> Self;
}

pub fn weight_recursive<C>(c: &C) -> C::WeightType
where
    C: BifurcateCoordinate,
{
    // Precondition: $\property{tree}(c)$
    if c.empty() {
        return C::WeightType::zero();
    }
    let mut l = C::WeightType::zero();
    let mut r = C::WeightType::zero();
    if c.has_left_successor() {
        l = weight_recursive(&c.left_successor());
    }
    if c.has_right_successor() {
        r = weight_recursive(&c.right_successor());
    }
    successor(l + r)
}

pub fn height_recursive<C>(c: &C) -> C::WeightType
where
    C: BifurcateCoordinate,
{
    // Precondition: $\property{tree}(c)$
    if c.empty() {
        return C::WeightType::zero();
    }
    let mut l = C::WeightType::zero();
    let mut r = C::WeightType::zero();
    if c.has_left_successor() {
        l = height_recursive(&c.left_successor());
    }
    if c.has_right_successor() {
        r = height_recursive(&c.right_successor());
    }
    successor(max(&l, &r).clone())
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
pub enum Visit {
    Pre,
    In_,
    Post,
}
use Visit::{In_, Post, Pre};

pub fn traverse_nonempty<C, Proc>(c: &C, mut proc: Proc) -> Proc
where
    C: BifurcateCoordinate,
    Proc: FnMut(Visit, &C),
{
    // Precondition: $\property{tree}(c) \wedge \neg \func{empty}(c)$
    proc(Pre, c);
    if c.has_left_successor() {
        proc = traverse_nonempty(&c.left_successor(), proc);
    }
    proc(In_, c);
    if c.has_right_successor() {
        proc = traverse_nonempty(&c.right_successor(), proc);
    }
    proc(Post, c);
    proc
}

pub trait BidirectionalBifurcateCoordinate: BifurcateCoordinate {
    fn has_predecessor(&self) -> bool;
    fn predecessor(&self) -> Self;
}

pub fn is_left_successor<T>(j: &T) -> bool
where
    T: BidirectionalBifurcateCoordinate,
{
    // Precondition: $\func{has\_predecessor}(j)$
    let i = j.predecessor();
    i.has_left_successor() && i.left_successor() == *j
}

pub fn is_right_successor<T>(j: &T) -> bool
where
    T: BidirectionalBifurcateCoordinate,
{
    // Precondition: $\func{has\_predecessor}(j)$
    let i = j.predecessor();
    i.has_right_successor() && i.right_successor() == *j
}

pub fn traverse_step<C>(v: &mut Visit, c: &mut C) -> i32
where
    C: BidirectionalBifurcateCoordinate,
{
    // Precondition: $\func{has\_predecessor}(c) \vee v \neq post$
    match v {
        Pre => {
            if c.has_left_successor() {
                *c = c.left_successor();
                return 1;
            }
            *v = In_;
            0
        }
        In_ => {
            if c.has_right_successor() {
                *v = Pre;
                *c = c.right_successor();
                return 1;
            }
            *v = Post;
            0
        }
        Post => {
            if is_left_successor(c) {
                *v = In_;
            }
            *c = c.predecessor();
            -1
        }
    }
}

pub fn reachable<C>(mut x: C, y: &C) -> bool
where
    C: BidirectionalBifurcateCoordinate,
{
    // Precondition: $\property{tree}(x)$
    if x.empty() {
        return false;
    }
    let root = x.clone();
    let mut v = Pre;
    loop {
        if x == *y {
            return true;
        }
        traverse_step(&mut v, &mut x);
        if x == root && v == Post {
            break;
        }
    }
    false
}

pub fn weight<C>(mut c: C) -> C::WeightType
where
    C: BidirectionalBifurcateCoordinate,
{
    // Precondition: $\property{tree}(c)$
    if c.empty() {
        return C::WeightType::zero();
    }
    let root = c.clone();
    let mut v = Pre;
    let mut n = C::WeightType::one(); // Invariant: $n$ is count of $\type{pre}$ visits so far
    loop {
        traverse_step(&mut v, &mut c);
        if v == Pre {
            n = successor(n);
        }
        if c == root && v == Post {
            break;
        }
    }
    n
}

pub fn height<C>(mut c: C) -> C::WeightType
where
    C: BidirectionalBifurcateCoordinate,
{
    // Precondition: $\property{tree}(c)$
    if c.empty() {
        return C::WeightType::zero();
    }
    let root = c.clone();
    let mut v = Pre;
    let mut n = C::WeightType::one(); // Invariant: $n$ is max of height of $\type{pre}$ visits so far
    let mut m = C::WeightType::one(); // Invariant: $m$ is height of current $\type{pre}$ visit
    loop {
        m = (m - C::WeightType::one()) + NumCast::from(traverse_step(&mut v, &mut c) + 1).unwrap();
        n = max(&n, &m).clone();
        if c == root && v == Post {
            break;
        }
    }
    n
}

pub fn traverse<C, Proc>(mut c: C, mut proc: Proc) -> Proc
where
    C: BidirectionalBifurcateCoordinate,
    Proc: FnMut(&Visit, &C),
{
    // Precondition: $\property{tree}(c)$
    if c.empty() {
        return proc;
    }
    let root = c.clone();
    let mut v = Pre;
    proc(&Pre, &c);
    loop {
        traverse_step(&mut v, &mut c);
        proc(&v, &c);
        if c == root && v == Post {
            break;
        }
    }
    proc
}

// Exercise 7.3: Use traverse_step and the procedures of Chapter 2 to determine
// whether the descendants of a bidirectional bifurcate coordinate form a DAG

pub fn bifurcate_isomorphic_nonempty<C0, C1>(c0: &C0, c1: &C1) -> bool
where
    C0: BifurcateCoordinate,
    C1: BifurcateCoordinate,
{
    // Precondition:
    // $\property{tree}(c0) \wedge \property{tree}(c1) \wedge \neg \func{empty}(c0) \wedge \neg \func{empty}(c1)$
    if c0.has_left_successor() {
        if c1.has_left_successor() {
            if !bifurcate_isomorphic_nonempty(&c0.left_successor(), &c1.left_successor()) {
                return false;
            }
        } else {
            return false;
        }
    } else if c1.has_left_successor() {
        return false;
    }
    if c0.has_right_successor() {
        if c1.has_right_successor() {
            if !bifurcate_isomorphic_nonempty(&c0.right_successor(), &c1.right_successor()) {
                return false;
            }
        } else {
            return false;
        }
    } else if c1.has_right_successor() {
        return false;
    }
    true
}

pub fn bifurcate_isomorphic<C0, C1>(mut c0: C0, mut c1: C1) -> bool
where
    C0: BidirectionalBifurcateCoordinate,
    C1: BidirectionalBifurcateCoordinate,
{
    // Precondition: $\property{tree}(c0) \wedge \property{tree}(c1)$
    if c0.empty() {
        return c1.empty();
    }
    if c1.empty() {
        return false;
    }
    let root0 = c0.clone();
    let mut v0 = Pre;
    let mut v1 = Pre;
    loop {
        traverse_step(&mut v0, &mut c0);
        traverse_step(&mut v1, &mut c1);
        if v0 != v1 {
            return false;
        }
        if c0 == root0 && v0 == Post {
            return true;
        }
    }
}

pub fn lexicographical_equivalent<I0, I1, R>(f0: I0, l0: &I0, f1: I1, l1: &I1, r: &R) -> bool
where
    I0: Readable + Iterator,
    I1: Readable<ValueType = I0::ValueType> + Iterator,
    R: Relation<Domain = I0::ValueType>,
{
    // Precondition: $\property{readable\_bounded\_range}(f0, l0)$
    // Precondition: $\property{readable\_bounded\_range}(f1, l1)$
    // Precondition: $\property{equivalence}(r)$
    let p = find_mismatch(f0, l0, f1, l1, r);
    p.m0 == *l0 && p.m1 == *l1
}

pub fn lexicographical_equal<I0, I1>(f0: I0, l0: &I0, f1: I1, l1: &I1) -> bool
where
    I0: Readable + Iterator,
    I1: Readable<ValueType = I0::ValueType> + Iterator,
{
    lexicographical_equivalent(f0, l0, f1, l1, &Equal::default())
}

/*
// Could specialize to use lexicographic_equal for k > some cutoff
template<int k, typename I0, typename I1>
   requires(Readable(I0) && ForwardIterator(I0) &&
       Readable(I1) && ForwardIterator(I1) &&
       ValueType(I0) == ValueType(I1))
struct lexicographical_equal_k
{
   bool operator()(I0 f0, I1 f1)
   {
       if (source(f0) != source(f1)) return false;
       return lexicographical_equal_k<k - 1, I0, I1>()(successor(f0), successor(f1));
   }
};
*/

/*
template<typename I0, typename I1>
struct lexicographical_equal_k<0, I0, I1>
{
   bool operator()(I0, I1)
   {
       return true;
   }
};
*/

pub fn bifurcate_equivalent_nonempty<C0, C1, R>(c0: &C0, c1: &C1, r: &R) -> bool
where
    C0: Readable + BifurcateCoordinate,
    C1: Readable<ValueType = C0::ValueType> + BifurcateCoordinate,
    R: Relation<Domain = C0::ValueType>,
{
    // Precondition: $\property{readable\_tree}(c0) \wedge \property{readable\_tree}(c1)$
    // Precondition: $\neg \func{empty}(c0) \wedge \neg \func{empty}(c1)$
    // Precondition: $\property{equivalence}(r)$
    if !r.call(c0.source(), c1.source()) {
        return false;
    }
    if c0.has_left_successor() {
        if c1.has_left_successor() {
            if !bifurcate_equivalent_nonempty(&c0.left_successor(), &c1.left_successor(), r) {
                return false;
            }
        } else {
            return false;
        }
    } else if c1.has_left_successor() {
        return false;
    }
    if c0.has_right_successor() {
        if c1.has_right_successor() {
            if !bifurcate_equivalent_nonempty(&c0.right_successor(), &c1.right_successor(), r) {
                return false;
            }
        } else {
            return false;
        }
    } else if c1.has_right_successor() {
        return false;
    }
    true
}

pub fn bifurcate_equivalent<C0, C1, R>(mut c0: C0, mut c1: C1, r: &R) -> bool
where
    C0: Readable + BidirectionalBifurcateCoordinate,
    C1: Readable<ValueType = C0::ValueType> + BidirectionalBifurcateCoordinate,
    R: Relation<Domain = C0::ValueType>,
{
    // Precondition: $\property{readable\_tree}(c0) \wedge \property{readable\_tree}(c1)$
    // Precondition: $\property{equivalence}(r)$
    if c0.empty() {
        return c1.empty();
    }
    if c1.empty() {
        return false;
    }
    let root0 = c0.clone();
    let mut v0 = Pre;
    let mut v1 = Pre;
    loop {
        if v0 == Pre && !r.call(c0.source(), c1.source()) {
            return false;
        }
        traverse_step(&mut v0, &mut c0);
        traverse_step(&mut v1, &mut c1);
        if v0 != v1 {
            return false;
        }
        if c0 == root0 && v0 == Post {
            return true;
        }
    }
}

pub fn bifurcate_equal<C0, C1>(c0: C0, c1: C1) -> bool
where
    C0: Readable + BidirectionalBifurcateCoordinate,
    C1: Readable<ValueType = C0::ValueType> + BidirectionalBifurcateCoordinate,
{
    bifurcate_equivalent(c0, c1, &Equal::default())
}

pub fn lexicographical_compare<I0, I1, R>(mut f0: I0, l0: &I0, mut f1: I1, l1: &I1, r: &R) -> bool
where
    I0: Readable + Iterator,
    I1: Readable<ValueType = I0::ValueType> + Iterator,
    R: Relation<Domain = I0::ValueType>,
{
    // Precondition: $\property{readable\_bounded\_range}(f0, l0)$
    // Precondition: $\property{readable\_bounded\_range}(f1, l1)$
    // Precondition: $\property{weak\_ordering}(r)$
    loop {
        if f1 == *l1 {
            return false;
        }
        if f0 == *l0 {
            return true;
        }
        if r.call(f0.source(), f1.source()) {
            return true;
        }
        if r.call(f1.source(), f0.source()) {
            return false;
        }
        f0 = f0.successor();
        f1 = f1.successor();
    }
}

pub fn lexicographical_less<I0, I1>(f0: I0, l0: &I0, f1: I1, l1: &I1) -> bool
where
    I0: Readable + Iterator,
    I1: Readable<ValueType = I0::ValueType> + Iterator,
    I0::ValueType: TotallyOrdered,
{
    lexicographical_compare(f0, l0, f1, l1, &Less::default())
}

/*
template<int k, typename I0, typename I1>
   requires(Readable(I0) && ForwardIterator(I0) &&
       Readable(I1) && ForwardIterator(I1) &&
       ValueType(I0) == ValueType(I1))
struct lexicographical_less_k
{
   bool operator()(I0 f0, I1 f1)
   {
       if (source(f0) < source(f1)) return true;
       if (source(f0) > source(f1)) return false;
       return lexicographical_less_k<k - 1, I0, I1>()(
           successor(f0),
           successor(f1));
   }
};

template<typename I0, typename I1>
struct lexicographical_less_k<0, I0, I1>
{
   bool operator()(I0, I1)
   {
       return false;
   }
};
*/

// Exercise 7.6: bifurcate_compare_nonempty (using 3-way comparsion)

// concept Comparator3Way(F) is
//     HomogeneousFunction(F)
//  /\ Arity(F) = 2
//  /\ Codomain(F) = int

// property(F : Comparator3Way)
// three_way_compare : F
//  f |- (all a,b in Domain(F)) f(a, b) in {-1, 0, 1}

//  Also need axioms equivalent to weak_order : transitivity, etc.
//  We could relax this to OrderedAdditiveGroup
//  (allowing subtraction as the comparator for numbers)
//  Should sense of positive/negative be flipped?

pub trait Compare3Way {
    type Domain;
    fn call(&self, a: &Self::Domain, b: &Self::Domain) -> i32;
}

pub struct Comparator3Way<R> {
    r: R,
}

impl<R> Comparator3Way<R>
where
    R: Relation,
{
    pub fn new(r: R) -> Self {
        // Precondition: $\property{weak\_ordering}(r)$
        Self { r }
        // Postcondition: three_way_compare(comparator_3_way(r))
    }
}

impl<R> Compare3Way for Comparator3Way<R>
where
    R: Relation,
{
    type Domain = R::Domain;
    fn call(&self, a: &Self::Domain, b: &Self::Domain) -> i32 {
        if self.r.call(a, b) {
            return 1;
        }
        if self.r.call(b, a) {
            return -1;
        }
        0
    }
}

pub fn lexicographical_compare_3way<I0, I1, F>(
    mut f0: I0,
    l0: &I0,
    mut f1: I1,
    l1: &I1,
    comp: &F,
) -> i32
where
    I0: Readable + Iterator,
    I1: Readable<ValueType = I0::ValueType> + Iterator,
    F: Compare3Way<Domain = I0::ValueType>,
{
    // Precondition: $\property{readable\_bounded\_range}(f0, l0)$
    // Precondition: $\property{readable\_bounded\_range}(f1, l1)$
    // Precondition: $\property{three\_way\_compare}(comp)$
    loop {
        if f0 == *l0 {
            if f1 == *l1 {
                return 0;
            } else {
                return 1;
            }
        }
        if f1 == *l1 {
            return -1;
        }
        let tmp = comp.call(f0.source(), f1.source());
        if tmp != 0 {
            return tmp;
        }
        f0 = f0.successor();
        f1 = f1.successor();
    }
}

pub fn bifurcate_compare_nonempty<C0, C1, F>(c0: &C0, c1: &C1, comp: &F) -> i32
where
    C0: Readable + BifurcateCoordinate,
    C1: Readable<ValueType = C0::ValueType> + BifurcateCoordinate,
    F: Compare3Way<Domain = C0::ValueType>,
{
    // Precondition: $\property{readable\_tree}(c0) \wedge \property{readable\_tree}(c1)$
    // Precondition: $\neg \func{empty}(c0) \wedge \neg \func{empty}(c1)$
    // Precondition: $\property{three\_way\_compare}(comp)$
    let mut tmp = comp.call(c0.source(), c1.source());
    if tmp != 0 {
        return tmp;
    }
    if c0.has_left_successor() {
        if c1.has_left_successor() {
            tmp = bifurcate_compare_nonempty(&c0.left_successor(), &c1.left_successor(), comp);
            if tmp != 0 {
                return tmp;
            }
        } else {
            return -1;
        }
    } else if c1.has_left_successor() {
        return 1;
    }
    if c0.has_right_successor() {
        if c1.has_right_successor() {
            tmp = bifurcate_compare_nonempty(&c0.right_successor(), &c1.right_successor(), comp);
            if tmp != 0 {
                return tmp;
            }
        } else {
            return -1;
        }
    } else if c1.has_right_successor() {
        return 1;
    }
    0
}

pub fn bifurcate_compare<C0, C1, R>(mut c0: C0, mut c1: C1, r: &R) -> bool
where
    C0: Readable + BidirectionalBifurcateCoordinate,
    C1: Readable<ValueType = C0::ValueType> + BidirectionalBifurcateCoordinate,
    R: Relation<Domain = C0::ValueType>,
{
    // Precondition: $\property{readable\_tree}(c0) \wedge
    //                \property{readable\_tree}(c1) \wedge
    //                \property{weak\_ordering}(r)$
    if c1.empty() {
        return false;
    }
    if c0.empty() {
        return true;
    }
    let root0 = c0.clone();
    let mut v0 = Pre;
    let mut v1 = Pre;
    loop {
        if v0 == Pre {
            if r.call(c0.source(), c1.source()) {
                return true;
            }
            if r.call(c1.source(), c0.source()) {
                return false;
            }
        }
        traverse_step(&mut v0, &mut c0);
        traverse_step(&mut v1, &mut c1);
        if v0 != v1 {
            return v0 > v1;
        };
        if c0 == root0 && v0 == Post {
            return false;
        }
    }
}

pub fn bifurcate_less<C0, C1>(c0: C0, c1: C1) -> bool
where
    C0: Readable + BidirectionalBifurcateCoordinate,
    C1: Readable<ValueType = C0::ValueType> + BidirectionalBifurcateCoordinate,
    C0::ValueType: TotallyOrdered,
{
    // Precondition: $\property{readable\_tree}(c0) \wedge
    //                \property{readable\_tree}(c1)
    bifurcate_compare(c0, c1, &Less::default())
}

#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub struct AlwaysFalse<T>(PhantomData<T>);

impl<T> Relation for AlwaysFalse<T>
where
    T: Regular,
{
    type Domain = T;
    #[must_use]
    fn call(&self, _: &T, _: &T) -> bool {
        false
    }
}

pub fn bifurcate_shape_compare<C0, C1>(c0: C0, c1: C1) -> bool
where
    C0: Readable + BidirectionalBifurcateCoordinate,
    C1: Readable<ValueType = C0::ValueType> + BidirectionalBifurcateCoordinate,
{
    // Precondition: $\property{readable\_tree}(c0) \wedge
    //                \property{readable\_tree}(c1)
    bifurcate_compare(c0, c1, &AlwaysFalse::default())
}

/*
//
//  Chapter 8. Coordinates with mutable successors
//


// Models of ForwardLinker, BackwardLinker, and BidirectionalLinker
// assuming a particular representation of links

template<typename I>
    requires(LinkedForwardIterator(I))
struct forward_linker
{
    void operator()(I x, I y)
    {
        sink(x.p).forward_link = y.p;
    }
};

template<typename I>
    requires(LinkableForwardIterator(I))
struct iterator_type< forward_linker<I> >
{
    typedef I type;
};

template<typename I>
    requires(LinkedBidirectionalIterator(I))
struct backward_linker
{
    void operator()(I x, I y)
    {
        sink(y.p).backward_link = x.p;
    }
};

template<typename I>
    requires(LinkedBidirectionalIterator(I))
struct iterator_type< backward_linker<I> >
{
    typedef I type;
};

template<typename I>
    requires(LinkedBidirectionalIterator(I))
struct bidirectional_linker
{
    void operator()(I x, I y)
    {
        sink(x.p).forward_link = y.p;
        sink(y.p).backward_link = x.p;
    }
};

template<typename I>
    requires(LinkedBidirectionalIterator(I))
struct iterator_type< bidirectional_linker<I> >
{
    typedef I type;
};
*/

pub fn advance_tail<I>(t: &mut I, f: &mut I)
where
    I: ForwardIterator,
{
    // Precondition: $\func{successor}(f)\text{ is defined}$
    *t = f.clone();
    *f = f.successor();
}

pub trait ForwardLinker: Regular {
    type IteratorType: ForwardIterator;
    fn call(&self, t: &mut Self::IteratorType, f: &mut Self::IteratorType);
}

pub struct LinkerToTail<S> {
    set_link: S,
}

impl<S> LinkerToTail<S>
where
    S: ForwardLinker,
{
    pub fn new(set_link: S) -> Self {
        Self { set_link }
    }
    pub fn call(&self, t: &mut S::IteratorType, f: &mut S::IteratorType) {
        // Precondition: $\func{successor}(f)\text{ is defined}$
        self.set_link.call(t, f);
        advance_tail(t, f);
    }
}

pub fn find_last<I>(mut f: I, l: &I) -> I
where
    I: ForwardIterator,
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge f \neq l$
    let mut t = I::default();
    loop {
        advance_tail(&mut t, &mut f);
        if f == *l {
            break;
        }
    }
    t
}

pub trait UnaryPseudoPredicate: UnaryPredicate {
    fn call(&mut self, x: &Self::Domain) -> bool;
}

enum SplitLinkedState {
    S0,
    S1,
    S2,
    S3,
    S4,
}

pub fn split_linked<I, S, Pred>(
    mut f: I,
    l: &I,
    p: &Pred,
    set_link: S,
) -> Pair<Pair<I, I>, Pair<I, I>>
where
    S: ForwardLinker<IteratorType = I>,
    I: Iterator,
    Pred: UnaryPseudoPredicate<Domain = I>,
{
    // Precondition: $\property{bounded\_range}(f, l)$
    let link_to_tail = LinkerToTail::new(set_link);
    let mut h0 = l.clone();
    let mut t0 = l.clone();
    let mut h1 = l.clone();
    let mut t1 = l.clone();
    let mut state = if f == *l {
        SplitLinkedState::S4
    } else if p.call(&f) {
        h1 = f.clone();
        advance_tail(&mut t1, &mut f);
        SplitLinkedState::S1
    } else {
        h0 = f.clone();
        advance_tail(&mut t0, &mut f);
        SplitLinkedState::S0
    };
    loop {
        state = match state {
            SplitLinkedState::S0 => {
                if f == *l {
                    SplitLinkedState::S4
                } else if p.call(&f) {
                    h1 = f.clone();
                    advance_tail(&mut t1, &mut f);
                    SplitLinkedState::S3
                } else {
                    advance_tail(&mut t0, &mut f);
                    SplitLinkedState::S0
                }
            }
            SplitLinkedState::S1 => {
                if f == *l {
                    SplitLinkedState::S4
                } else if p.call(&f) {
                    advance_tail(&mut t1, &mut f);
                    SplitLinkedState::S1
                } else {
                    h0 = f.clone();
                    advance_tail(&mut t0, &mut f);
                    SplitLinkedState::S2
                }
            }
            SplitLinkedState::S2 => {
                if f == *l {
                    SplitLinkedState::S4
                } else if p.call(&f) {
                    link_to_tail.call(&mut t1, &mut f);
                    SplitLinkedState::S3
                } else {
                    advance_tail(&mut t0, &mut f);
                    SplitLinkedState::S2
                }
            }
            SplitLinkedState::S3 => {
                if f == *l {
                    SplitLinkedState::S4
                } else if p.call(&f) {
                    advance_tail(&mut t1, &mut f);
                    SplitLinkedState::S3
                } else {
                    link_to_tail.call(&mut t0, &mut f);
                    SplitLinkedState::S2
                }
            }
            SplitLinkedState::S4 => {
                return Pair::new(Pair::new(h0, t0), Pair::new(h1, t1));
            }
        }
    }
}

// Exercise 8.1: Explain the postcondition of split_linked

pub trait PseudoRelation: Regular {
    type Domain0;
    type Domain1;
    fn call(&mut self, x: &Self::Domain0, y: &Self::Domain1) -> bool;
}

enum CombineLinkedNonemptyState {
    S0,
    S1,
    S2,
    S3,
}

pub fn combine_linked_nonempty<I, S, R>(
    mut f0: I,
    l0: I,
    mut f1: I,
    l1: I,
    mut r: R,
    set_link: &S,
) -> Triple<I, I, I>
where
    I: Iterator,
    S: ForwardLinker<IteratorType = I>,
    R: PseudoRelation<Domain0 = I, Domain1 = I>,
{
    // Precondition: $\property{bounded\_range}(f0, l0) \wedge
    //                \property{bounded\_range}(f1, l1)$
    // Precondition: $f0 \neq l0 \wedge f1 \neq l1 \wedge
    //                \property{disjoint}(f0, l0, f1, l1)$
    let link_to_tail = LinkerToTail::new(set_link.clone());
    let h;
    let mut t = I::default();
    let mut state = if r.call(&f1, &f0) {
        h = f1.clone();
        advance_tail(&mut t, &mut f1);
        CombineLinkedNonemptyState::S1
    } else {
        h = f0.clone();
        advance_tail(&mut t, &mut f0);
        CombineLinkedNonemptyState::S0
    };
    loop {
        state = match state {
            CombineLinkedNonemptyState::S0 => {
                if f0 == l0 {
                    CombineLinkedNonemptyState::S2
                } else if r.call(&f1, &f0) {
                    link_to_tail.call(&mut t, &mut f1);
                    CombineLinkedNonemptyState::S1
                } else {
                    advance_tail(&mut t, &mut f0);
                    CombineLinkedNonemptyState::S0
                }
            }
            CombineLinkedNonemptyState::S1 => {
                if f1 == l1 {
                    CombineLinkedNonemptyState::S3
                } else if r.call(&f1, &f0) {
                    advance_tail(&mut t, &mut f1);
                    CombineLinkedNonemptyState::S1
                } else {
                    link_to_tail.call(&mut t, &mut f0);
                    CombineLinkedNonemptyState::S0
                }
            }
            CombineLinkedNonemptyState::S2 => {
                set_link.call(&mut t, &mut f1);
                return Triple::new(h, t, l1);
            }
            CombineLinkedNonemptyState::S3 => {
                set_link.call(&mut t, &mut f0);
                return Triple::new(h, t, l0);
            }
        }
    }
}

// Exercise 8.2: combine_linked

pub struct LinkerToHead<I, S>
where
    I: ForwardIterator,
    S: ForwardLinker<IteratorType = I>,
{
    set_link: S,
}

impl<I, S> LinkerToHead<I, S>
where
    I: ForwardIterator,
    S: ForwardLinker<IteratorType = I>,
{
    pub fn new(set_link: S) -> Self {
        Self { set_link }
    }
    pub fn call(&self, mut h: &mut I, mut f: &mut I) {
        // Precondition: $\func{successor}(f)$ is defined
        let tmp = f.successor();
        self.set_link.call(&mut f, &mut h);
        *h = f.clone();
        *f = tmp;
    }
}

pub fn reverse_append<I, S>(mut f: I, l: &I, mut h: I, set_link: S) -> I
where
    I: ForwardIterator,
    S: ForwardLinker<IteratorType = I>,
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge h \notin [f, l)$
    let link_to_head = LinkerToHead::new(set_link);
    while f != *l {
        link_to_head.call(&mut h, &mut f);
    }
    h
}

pub struct PredicateSource<I, P> {
    p: P,
    marker: PhantomData<I>,
}

impl<I, P> PredicateSource<I, P> {
    pub fn new(p: P) -> Self {
        Self {
            p,
            marker: PhantomData,
        }
    }
}

impl<I, P> UnaryPseudoPredicate for PredicateSource<I, P>
where
    I: Readable,
    P: UnaryPseudoPredicate<Domain = I::ValueType>,
{
    fn call(&mut self, i: &I) -> bool {
        self.p.call(i.source())
    }
}

impl<I, P> UnaryPredicate for PredicateSource<I, P>
where
    I: Readable,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    type Domain = I;
    fn call(&self, i: &I) -> bool {
        self.p.call(i.source())
    }
}

pub fn partition_linked<I, S, P>(f: I, l: &I, p: P, set_link: S) -> Pair<Pair<I, I>, Pair<I, I>>
where
    I: Readable + ForwardIterator,
    S: ForwardLinker<IteratorType = I>,
    P: UnaryPseudoPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{bounded\_range}(f, l)$
    let ps = PredicateSource::new(p);
    split_linked(f, l, &ps, set_link)
}

#[derive(Clone, Default, Eq, PartialEq)]
pub struct RelationSource<I0, I1, R>
where
    I0: Readable,
    I1: Readable<ValueType = I0::ValueType>,
    R: Relation<Domain = I0::ValueType>,
{
    r: R,
    marker: PhantomData<(I0, I1)>,
}

impl<I0, I1, R> RelationSource<I0, I1, R>
where
    I0: Readable,
    I1: Readable<ValueType = I0::ValueType>,
    R: Relation<Domain = I0::ValueType>,
{
    pub fn new(r: R) -> Self {
        Self {
            r,
            marker: PhantomData,
        }
    }
}

impl<I0, I1, R> PseudoRelation for RelationSource<I0, I1, R>
where
    I0: Readable,
    I1: Readable<ValueType = I0::ValueType>,
    R: Relation<Domain = I0::ValueType>,
{
    type Domain0 = I0;
    type Domain1 = I1;
    fn call(&mut self, i0: &Self::Domain0, i1: &Self::Domain1) -> bool {
        self.r.call(i0.source(), i1.source())
    }
}

impl<I0, I1, R> BinaryPredicate for RelationSource<I0, I1, R>
where
    I0: Readable,
    I1: Readable<ValueType = I0::ValueType>,
    R: Relation<Domain = I0::ValueType>,
{
    type InputType0 = I0;
    type InputType1 = I1;
    fn call(&self, i0: &Self::InputType0, i1: &Self::InputType1) -> bool {
        self.r.call(i0.source(), i1.source())
    }
}

pub fn merge_linked_nonempty<I, S, R>(
    f0: I,
    l0: I,
    f1: I,
    mut l1: I,
    r: R,
    set_link: &S,
) -> Pair<I, I>
where
    I: Readable + ForwardIterator,
    S: ForwardLinker<IteratorType = I>,
    R: Relation<Domain = I::ValueType>,
{
    // Precondition: $f0 \neq l0 \wedge f1 \neq l1$
    // Precondition: $\property{increasing\_range}(f0, l0, r)$
    // Precondition: $\property{increasing\_range}(f1, l1, r)$
    let rs = RelationSource::new(r);
    let t = combine_linked_nonempty(f0, l0, f1, l1.clone(), rs, set_link);
    set_link.call(&mut find_last(t.m1, &t.m2), &mut l1);
    Pair::new(t.m0, l1)
}

pub fn sort_linked_nonempty_n<I, S, R>(f: I, n: I::DistanceType, r: R, set_link: &S) -> Pair<I, I>
where
    I: Readable + ForwardIterator,
    S: ForwardLinker<IteratorType = I>,
    R: Relation<Domain = I::ValueType>,
{
    // Precondition: $\property{counted\_range}(f, n) \wedge
    //                n > 0 \wedge \func{weak\_ordering}(r)$
    if n == I::DistanceType::one() {
        return Pair::new(f.clone(), f.successor());
    }
    let h = half_nonnegative(n.clone());
    let p0 = sort_linked_nonempty_n(f, h.clone(), r.clone(), set_link);
    let p1 = sort_linked_nonempty_n(p0.m1.clone(), n - h, r.clone(), set_link);
    merge_linked_nonempty(p0.m0, p0.m1, p1.m0, p1.m1, r, set_link)
}

// Exercise 8.3: Complexity of sort_linked_nonempty_n

// Exercise 8.4: unique

pub trait LinkedBifurcateCoordinate: BifurcateCoordinate {
    fn set_left_successor(&mut self, x: &mut Self);
    fn set_right_successor(&mut self, x: &mut Self);
}

pub trait EmptyLinkedBifurcateCoordinate: LinkedBifurcateCoordinate {}

pub fn tree_rotate<C>(curr: &mut C, mut prev: &mut C)
where
    C: EmptyLinkedBifurcateCoordinate,
{
    // Precondition: $\neg \func{empty}(curr)$
    let tmp = curr.left_successor();
    curr.set_left_successor(&mut curr.right_successor());
    curr.set_right_successor(&mut prev);
    if tmp.empty() {
        *prev = tmp;
        return;
    }
    *prev = curr.clone();
    *curr = tmp;
}

pub trait UnaryProcedure {
    type Domain;
    fn call(&mut self, x: &Self::Domain);
}

pub fn traverse_rotating<C, Proc>(c: &C, mut proc: Proc) -> Proc
where
    C: EmptyLinkedBifurcateCoordinate,
    Proc: UnaryProcedure<Domain = C>,
{
    // Precondition: $\property{tree}(c)$
    if c.empty() {
        return proc;
    }
    let mut curr = c.clone();
    let mut prev = C::default();
    loop {
        proc.call(&curr);
        tree_rotate(&mut curr, &mut prev);
        if curr == *c {
            break;
        }
    }
    loop {
        proc.call(&curr);
        tree_rotate(&mut curr, &mut prev);
        if curr == *c {
            break;
        }
    }
    proc.call(&curr);
    tree_rotate(&mut curr, &mut prev);
    proc
}

// Exercise 8.5: Diagram each state of traverse_rotating
// for a complete binary tree with 7 nodes

#[derive(Default)]
pub struct Counter<T, N>
where
    N: Integer,
{
    n: N,
    marker: PhantomData<T>,
}

impl<T, N> Counter<T, N>
where
    N: Integer,
{
    pub fn new(n: N) -> Self {
        Self {
            n,
            marker: PhantomData,
        }
    }
}

impl<T, N> UnaryProcedure for Counter<T, N>
where
    N: Integer,
{
    type Domain = T;
    fn call(&mut self, _: &T) {
        self.n = successor(self.n.clone());
    }
}

pub fn weight_rotating<C>(c: &C) -> C::WeightType
where
    C: EmptyLinkedBifurcateCoordinate,
{
    // Precondition: $\property{tree}(c)$
    traverse_rotating(c, Counter::<C, C::WeightType>::default()).n / NumCast::from(3).unwrap()
}

pub struct PhasedApplicator<N, Proc>
where
    N: Integer,
    Proc: UnaryProcedure,
{
    period: N,
    phase: N,
    n: N,
    // Invariant: $n, phase \in [0, period)$
    proc: Proc,
}

impl<N, Proc> PhasedApplicator<N, Proc>
where
    N: Integer,
    Proc: UnaryProcedure,
{
    pub fn new(period: N, phase: N, n: N, proc: Proc) -> Self {
        Self {
            period,
            phase,
            n,
            proc,
        }
    }
}

impl<N, Proc> UnaryProcedure for PhasedApplicator<N, Proc>
where
    N: Integer,
    Proc: UnaryProcedure,
{
    type Domain = Proc::Domain;
    fn call(&mut self, x: &Self::Domain) {
        if self.n == self.phase {
            self.proc.call(x);
        }
        self.n = successor(self.n.clone());
        if self.n == self.period {
            self.n = N::zero();
        }
    }
}

pub fn traverse_phased_rotating<C, Proc>(c: &C, phase: i32, proc: Proc) -> Proc
where
    C: EmptyLinkedBifurcateCoordinate,
    Proc: UnaryProcedure<Domain = C>,
{
    // Precondition: $\property{tree}(c) \wedge 0 \leq phase < 3$
    let applicator = PhasedApplicator::<i32, Proc>::new(3, phase, 0, proc);
    traverse_rotating(c, applicator).proc
}

//
//  Chapter 9. Copying
//

pub trait Writable: Reference {
    fn sink(&mut self) -> &mut Self::ValueType;
}

pub fn copy_step<I, O>(f_i: &mut I, f_o: &mut O)
where
    I: Readable + Iterator,
    O: Writable<ValueType = I::ValueType> + Iterator,
{
    // Precondition: $\func{source}(f_i)$ and $\func{sink}(f_o)$ are defined
    *f_o.sink() = f_i.source().clone();
    *f_i = f_i.successor();
    *f_o = f_o.successor();
}

pub fn copy<I, O>(mut f_i: I, l_i: &I, mut f_o: O) -> O
where
    I: Readable + Iterator,
    O: Writable<ValueType = I::ValueType> + Iterator,
{
    // Precondition:
    // $\property{not\_overlapped\_forward}(f_i, l_i, f_o, f_o + (l_i - f_i))$
    while f_i != *l_i {
        copy_step(&mut f_i, &mut f_o);
    }
    f_o
}

pub fn fill_step<I>(f_o: &mut I, x: &I::ValueType)
where
    I: Writable + Iterator,
{
    *f_o.sink() = x.clone();
    *f_o = f_o.successor();
}

pub fn fill<I>(mut f: I, l: &I, x: &I::ValueType) -> I
where
    I: Writable + Iterator,
{
    while f != *l {
        fill_step(&mut f, x);
    }
    f
}

pub fn iota<O>(n: &O::ValueType, o: O) -> O
where
    O: Writable + Iterator,
    O::ValueType: Integer + Iterator + Readable<ValueType = O::ValueType>, // like APL $\iota$
{
    // Precondition: $\property{writable\_counted\_range}(o, n) \wedge n \geq 0$
    copy(O::ValueType::zero(), n, o)
}

// Useful for testing in conjunction with iota
pub fn equal_iota<I>(mut f: I, l: &I, mut n: I::ValueType /*= 0*/) -> bool
where
    I: Readable + Iterator,
    I::ValueType: Integer,
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    while f != *l {
        if *f.source() != n {
            return false;
        }
        n = successor(n);
        f = f.successor();
    }
    true
}

pub fn copy_bounded<I, O>(mut f_i: I, l_i: &I, mut f_o: O, l_o: &O) -> Pair<I, O>
where
    I: Readable + Iterator,
    O: Writable<ValueType = I::ValueType> + Iterator,
{
    // Precondition: $\property{not\_overlapped\_forward}(f_i, l_i, f_o, l_o)$
    while f_i != *l_i && f_o != *l_o {
        copy_step(&mut f_i, &mut f_o);
    }
    Pair::new(f_i, f_o)
}

pub fn count_down<N>(n: &mut N) -> bool
where
    N: Integer,
{
    // Precondition: $n \geq 0$
    if zero(n) {
        return false;
    }
    *n = predecessor(n.clone());
    true
}

pub fn copy_n<I, O, N>(mut f_i: I, mut n: N, mut f_o: O) -> Pair<I, O>
where
    I: Readable + Iterator,
    O: Writable<ValueType = I::ValueType> + Iterator,
    N: Integer,
{
    // Precondition: $\property{not\_overlapped\_forward}(f_i, f_i+n, f_o, f_o+n)$
    while count_down(&mut n) {
        copy_step(&mut f_i, &mut f_o);
    }
    Pair::new(f_i, f_o)
}

pub fn fill_n<I>(mut f: I, mut n: I::DistanceType, x: &I::ValueType) -> I
where
    I: Writable + Iterator,
{
    while count_down(&mut n) {
        fill_step(&mut f, x);
    }
    f
}

pub fn copy_backward_step<I, O>(l_i: &mut I, l_o: &mut O)
where
    I: Readable + BidirectionalIterator,
    O: Writable<ValueType = I::ValueType> + BidirectionalIterator,
{
    // Precondition: $\func{source}(\property{predecessor}(l_i))$ and
    //               $\func{sink}(\property{predecessor}(l_o))$
    //               are defined
    *l_i = l_i.predecessor();
    *l_o = l_o.predecessor();
    *l_o.sink() = l_i.source().clone();
}

pub fn copy_backward<I, O>(f_i: &I, mut l_i: I, mut l_o: O) -> O
where
    I: Readable + BidirectionalIterator,
    O: Writable<ValueType = I::ValueType> + BidirectionalIterator,
{
    // Precondition: $\property{not\_overlapped\_backward}(f_i, l_i, l_o-(l_i-f_i), l_o)$
    while *f_i != l_i {
        copy_backward_step(&mut l_i, &mut l_o);
    }
    l_o
}

pub fn copy_backward_n<I, O>(mut l_i: I, mut n: I::DistanceType, mut l_o: O) -> Pair<I, O>
where
    I: Readable + BidirectionalIterator,
    O: Writable<ValueType = I::ValueType> + BidirectionalIterator,
{
    while count_down(&mut n) {
        copy_backward_step(&mut l_i, &mut l_o);
    }
    Pair::new(l_i, l_o)
}

pub fn reverse_copy_step<I, O>(l_i: &mut I, f_o: &mut O)
where
    I: Readable + BidirectionalIterator,
    O: Writable<ValueType = I::ValueType> + Iterator,
{
    // Precondition: $\func{source}(\func{predecessor}(l_i))$ and
    //               $\func{sink}(f_o)$ are defined
    *l_i = l_i.predecessor();
    *f_o.sink() = l_i.source().clone();
    *f_o = f_o.successor();
}

pub fn reverse_copy_backward_step<I, O>(f_i: &mut I, l_o: &mut O)
where
    I: Readable + Iterator,
    O: Writable<ValueType = I::ValueType> + BidirectionalIterator,
{
    // Precondition: $\func{source}(f_i)$ and
    //               $\func{sink}(\property{predecessor}(l_o))$ are defined
    *l_o = l_o.predecessor();
    *l_o.sink() = f_i.source().clone();
    *f_i = f_i.successor();
}

pub fn reverse_copy<I, O>(f_i: &I, mut l_i: I, mut f_o: O) -> O
where
    I: Readable + BidirectionalIterator,
    O: Writable<ValueType = I::ValueType> + Iterator,
{
    // Precondition: $\property{not\_overlapped}(f_i, l_i, f_o, f_o+(l_i-f_i))$
    while *f_i != l_i {
        reverse_copy_step(&mut l_i, &mut f_o);
    }
    f_o
}

pub fn reverse_copy_backward<I, O>(mut f_i: I, l_i: &I, mut l_o: O) -> O
where
    I: Readable + Iterator,
    O: Writable<ValueType = I::ValueType> + BidirectionalIterator,
{
    // Precondition: $\property{not\_overlapped}(f_i, l_i, l_o-(l_i-f_i), l_o)$
    while f_i != *l_i {
        reverse_copy_backward_step(&mut f_i, &mut l_o);
    }
    l_o
}

pub fn copy_select<I, O, P>(mut f_i: I, l_i: &I, mut f_t: O, p: &P) -> O
where
    I: Readable + Iterator,
    O: Writable<ValueType = I::ValueType> + Iterator,
    P: UnaryPredicate<Domain = I>,
{
    // Precondition: $\property{not\_overlapped\_forward}(f_i, l_i, f_t, f_t+n_t)$
    // where $n_t$ is an upper bound for the number of iterators satisfying $p$
    while f_i != *l_i {
        if p.call(&f_i) {
            copy_step(&mut f_i, &mut f_t);
        } else {
            f_i = f_i.successor();
        }
    }
    f_t
}

pub fn copy_if<I, O, P>(f_i: I, l_i: &I, f_t: O, p: P) -> O
where
    I: Readable + Iterator,
    O: Writable<ValueType = I::ValueType> + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: same as for $\func{copy\_select}$
    let ps = PredicateSource::new(p);
    copy_select(f_i, l_i, f_t, &ps)
}

pub fn split_copy<I, OF, OT, P>(
    mut f_i: I,
    l_i: &I,
    mut f_f: OF,
    mut f_t: OT,
    p: &P,
) -> Pair<OF, OT>
where
    I: Readable + Iterator,
    OF: Writable<ValueType = I::ValueType> + Iterator,
    OT: Writable<ValueType = I::ValueType> + Iterator,
    P: UnaryPredicate<Domain = I>,
{
    // Precondition: see section 9.3 of Elements of Programming
    while f_i != *l_i {
        if p.call(&f_i) {
            copy_step(&mut f_i, &mut f_t);
        } else {
            copy_step(&mut f_i, &mut f_f);
        }
    }
    Pair::new(f_f, f_t)
}

pub fn split_copy_n<I, OF, OT, P>(
    mut f_i: I,
    mut n_i: I::DistanceType,
    mut f_f: OF,
    mut f_t: OT,
    p: &P,
) -> Pair<OF, OT>
where
    I: Readable + Iterator,
    OF: Writable<ValueType = I::ValueType> + Iterator,
    OT: Writable<ValueType = I::ValueType> + Iterator,
    P: UnaryPredicate<Domain = I>,
{
    // Precondition: see exercise 9.2 of Elements of Programming
    while count_down(&mut n_i) {
        if p.call(&f_i) {
            copy_step(&mut f_i, &mut f_t);
        } else {
            copy_step(&mut f_i, &mut f_f);
        }
    }
    Pair::new(f_f, f_t)
}

pub fn partition_copy<I, OF, OT, P>(f_i: I, l_i: &I, f_f: OF, f_t: OT, p: P) -> Pair<OF, OT>
where
    I: Readable + Iterator,
    OF: Writable<ValueType = I::ValueType> + Iterator,
    OT: Writable<ValueType = I::ValueType> + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: same as $\func{split\_copy}$
    let ps = PredicateSource::new(p);
    split_copy(f_i, l_i, f_f, f_t, &ps)
}

pub fn partition_copy_n<I, OF, OT, P>(
    f_i: I,
    n: I::DistanceType,
    f_f: OF,
    f_t: OT,
    p: P,
) -> Pair<OF, OT>
where
    I: Readable + Iterator,
    OF: Writable<ValueType = I::ValueType> + Iterator,
    OT: Writable<ValueType = I::ValueType> + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: see $\func{partition_copy}$
    let ps = PredicateSource::new(p);
    split_copy_n(f_i, n, f_f, f_t, &ps)
}

pub trait BinaryPredicate {
    type InputType0;
    type InputType1;
    fn call(&self, x: &Self::InputType0, y: &Self::InputType1) -> bool;
}

pub fn combine_copy<I0, I1, O, R>(
    mut f_i0: I0,
    l_i0: &I0,
    mut f_i1: I1,
    l_i1: &I1,
    mut f_o: O,
    r: &R,
) -> O
where
    I0: Readable + Iterator,
    I1: Readable<ValueType = I0::ValueType> + Iterator,
    O: Writable<ValueType = I0::ValueType> + Iterator,
    R: BinaryPredicate<InputType0 = I1, InputType1 = I0>,
{
    // Precondition: see section 9.3 of Elements of Programming
    while f_i0 != *l_i0 && f_i1 != *l_i1 {
        if r.call(&f_i1, &f_i0) {
            copy_step(&mut f_i1, &mut f_o);
        } else {
            copy_step(&mut f_i0, &mut f_o);
        }
    }
    copy(f_i1, l_i1, copy(f_i0, l_i0, f_o))
}

pub fn combine_copy_n<I0, I1, O, R>(
    mut f_i0: I0,
    mut n_i0: I0::DistanceType,
    mut f_i1: I1,
    mut n_i1: I1::DistanceType,
    mut f_o: O,
    r: &R,
) -> Triple<I0, I1, O>
where
    I0: Readable + Iterator,
    I1: Readable<ValueType = I0::ValueType> + Iterator,
    O: Writable<ValueType = I0::ValueType> + Iterator,
    R: BinaryPredicate<InputType0 = I1, InputType1 = I0>,
{
    // Precondition: see $\func{combine_copy}$
    loop {
        if zero(&n_i0) {
            let p = copy_n(f_i1, n_i1, f_o);
            return Triple::new(f_i0, p.m0, p.m1);
        }
        if zero(&n_i1) {
            let p = copy_n(f_i0, n_i0, f_o);
            return Triple::new(p.m0, f_i1, p.m1);
        }
        if r.call(&f_i1, &f_i0) {
            copy_step(&mut f_i1, &mut f_o);
            n_i1 = predecessor(n_i1);
        } else {
            copy_step(&mut f_i0, &mut f_o);
            n_i0 = predecessor(n_i0);
        }
    }
}

pub fn combine_copy_backward<I0, I1, O, R>(
    f_i0: &I0,
    mut l_i0: I0,
    f_i1: &I1,
    mut l_i1: I1,
    mut l_o: O,
    r: &R,
) -> O
where
    I0: Readable + BidirectionalIterator,
    I1: Readable<ValueType = I0::ValueType> + BidirectionalIterator,
    O: Writable<ValueType = I0::ValueType> + BidirectionalIterator,
    R: BinaryPredicate<InputType0 = I1, InputType1 = I0>,
{
    // Precondition: see section 9.3 of Elements of Programming
    while *f_i0 != l_i0 && *f_i1 != l_i1 {
        if r.call(&l_i1.predecessor(), &l_i0.predecessor()) {
            copy_backward_step(&mut l_i0, &mut l_o);
        } else {
            copy_backward_step(&mut l_i1, &mut l_o);
        }
    }
    copy_backward(f_i0, l_i0, copy_backward(f_i1, l_i1, l_o))
}

pub fn combine_copy_backward_n<I0, I1, O, R>(
    mut l_i0: I0,
    mut n_i0: I0::DistanceType,
    mut l_i1: I1,
    mut n_i1: I1::DistanceType,
    mut l_o: O,
    r: &R,
) -> Triple<I0, I1, O>
where
    I0: Readable + BidirectionalIterator,
    I1: Readable<ValueType = I0::ValueType> + BidirectionalIterator,
    O: Writable<ValueType = I0::ValueType> + BidirectionalIterator,
    R: BinaryPredicate<InputType0 = I1, InputType1 = I0>,
{
    // Precondition: see $\func{combine\_copy\_backward}$
    loop {
        if zero(&n_i0) {
            let p = copy_backward_n(l_i1, n_i1, l_o);
            return Triple::new(l_i0, p.m0, p.m1);
        }
        if zero(&n_i1) {
            let p = copy_backward_n(l_i0, n_i0, l_o);
            return Triple::new(p.m0, l_i1, p.m1);
        }
        if r.call(&l_i1.predecessor(), &l_i0.predecessor()) {
            copy_backward_step(&mut l_i0, &mut l_o);
            n_i0 = predecessor(n_i0);
        } else {
            copy_backward_step(&mut l_i1, &mut l_o);
            n_i1 = predecessor(n_i1);
        }
    }
}

pub fn merge_copy<I0, I1, O, R>(f_i0: I0, l_i0: &I0, f_i1: I1, l_i1: &I1, f_o: O, r: R) -> O
where
    I0: Readable + Iterator,
    I1: Readable<ValueType = I0::ValueType> + Iterator,
    O: Writable<ValueType = I0::ValueType> + Iterator,
    R: Relation<Domain = I0::ValueType>,
{
    // Precondition: in addition to that for $\func{combine\_copy}$:
    // \hspace*{1em} $\property{weak\_ordering}(r) \wedge {}$
    // \hspace*{1em} $\func{increasing\_range}(f_{i_0}, l_{i_0}, r) \wedge
    //                \property{increasing\_range}(f_{i_1}, l_{i_1}, r)$
    let rs = RelationSource::new(r);
    combine_copy(f_i0, l_i0, f_i1, l_i1, f_o, &rs)
}

pub fn merge_copy_n<I0, I1, O, R>(
    f_i0: I0,
    n_i0: I0::DistanceType,
    f_i1: I1,
    n_i1: I1::DistanceType,
    o: O,
    r: R,
) -> Triple<I0, I1, O>
where
    I0: Readable + Iterator,
    I1: Readable<ValueType = I0::ValueType> + Iterator,
    O: Writable<ValueType = I0::ValueType> + Iterator,
    R: Relation<Domain = I0::ValueType>,
{
    // Precondition: see $\func{merge\_copy}$
    let rs = RelationSource::new(r);
    combine_copy_n(f_i0, n_i0, f_i1, n_i1, o, &rs)
}

pub fn merge_copy_backward<I0, I1, O, R>(
    f_i0: &I0,
    l_i0: I0,
    f_i1: &I1,
    l_i1: I1,
    l_o: O,
    r: R,
) -> O
where
    I0: Readable + BidirectionalIterator,
    I1: Readable<ValueType = I0::ValueType> + BidirectionalIterator,
    O: Writable<ValueType = I0::ValueType> + BidirectionalIterator,
    R: Relation<Domain = I0::ValueType>,
{
    // Precondition: in addition to that for $\func{combine\_copy\_backward}$:
    //               $\property{weak\_ordering}(r) \wedge {}$
    //               $\func{increasing\_range}(f_{i_0}, l_{i_0}, r) \wedge
    //                \property{increasing\_range}(f_{i_1}, l_{i_1}, r)$
    let rs = RelationSource::new(r);
    combine_copy_backward(f_i0, l_i0, f_i1, l_i1, l_o, &rs)
}

pub fn merge_copy_backward_n<I0, I1, O, R>(
    l_i0: I0,
    n_i0: I0::DistanceType,
    l_i1: I1,
    n_i1: I1::DistanceType,
    l_o: O,
    r: R,
) -> Triple<I0, I1, O>
where
    I0: Readable + BidirectionalIterator,
    I1: Readable<ValueType = I0::ValueType> + BidirectionalIterator,
    O: Writable<ValueType = I0::ValueType> + BidirectionalIterator,
    R: Relation<Domain = I0::ValueType>,
{
    // Precondition: see $\func{merge\_copy\_backward}$
    let rs = RelationSource::new(r);
    combine_copy_backward_n(l_i0, n_i0, l_i1, n_i1, l_o, &rs)
}

pub trait Mutable: Readable + Writable {}

pub fn exchange_values<I0, I1>(x: &mut I0, y: &mut I1)
where
    I0: Mutable,
    I1: Mutable<ValueType = I0::ValueType>,
{
    // Precondition: $\func{deref}(x)$ and $\func{deref}(y)$ are defined
    let t = x.source().clone();
    *x.sink() = y.source().clone();
    *y.sink() = t;
}

pub fn swap_step<I0, I1>(f0: &mut I0, f1: &mut I1)
where
    I0: Mutable + ForwardIterator,
    I1: Mutable<ValueType = I0::ValueType> + ForwardIterator,
{
    // Precondition: $\func{deref}(f_0)$ and $\func{deref}(f_1)$ are defined
    exchange_values(f0, f1);
    *f0 = f0.successor();
    *f1 = f1.successor();
}

pub fn swap_ranges<I0, I1>(mut f0: I0, l0: &I0, mut f1: I1) -> I1
where
    I0: Mutable + ForwardIterator,
    I1: Mutable<ValueType = I0::ValueType> + ForwardIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, l_0-f_0)$
    while f0 != *l0 {
        swap_step(&mut f0, &mut f1);
    }
    f1
}

pub fn swap_ranges_bounded<I0, I1>(mut f0: I0, l0: &I0, mut f1: I1, l1: &I1) -> Pair<I0, I1>
where
    I0: Mutable + ForwardIterator,
    I1: Mutable<ValueType = I0::ValueType> + ForwardIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition: $\property{mutable\_bounded\_range}(f_1, l_1)$
    while f0 != *l0 && f1 != *l1 {
        swap_step(&mut f0, &mut f1);
    }
    Pair::new(f0, f1)
}

pub fn swap_ranges_n<I0, I1, N>(mut f0: I0, mut f1: I1, mut n: N) -> Pair<I0, I1>
where
    I0: Mutable + ForwardIterator,
    I1: Mutable<ValueType = I0::ValueType> + ForwardIterator,
    N: Integer,
{
    // Precondition: $\property{mutable\_counted\_range}(f_0, n)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, n)$
    while count_down(&mut n) {
        swap_step(&mut f0, &mut f1);
    }
    Pair::new(f0, f1)
}

pub fn reverse_swap_step<I0, I1>(l0: &mut I0, f1: &mut I1)
where
    I0: Mutable + BidirectionalIterator,
    I1: Mutable<ValueType = I0::ValueType> + ForwardIterator,
{
    // Precondition: $\func{deref}(\func{predecessor}(l_0))$ and
    //               $\func{deref}(f_1)$ are defined
    *l0 = l0.predecessor();
    exchange_values(l0, f1);
    *f1 = f1.successor();
}

pub fn reverse_swap_ranges<I0, I1>(f0: &I0, mut l0: I0, mut f1: I1) -> I1
where
    I0: Mutable + BidirectionalIterator,
    I1: Mutable<ValueType = I0::ValueType> + ForwardIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, l_0-f_0)$
    while *f0 != l0 {
        reverse_swap_step(&mut l0, &mut f1);
    }
    f1
}

pub fn reverse_swap_ranges_bounded<I0, I1>(f0: &I0, mut l0: I0, mut f1: I1, l1: &I1) -> Pair<I0, I1>
where
    I0: Mutable + BidirectionalIterator,
    I1: Mutable<ValueType = I0::ValueType> + ForwardIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition:  $\property{mutable\_bounded\_range}(f_1, l_1)$
    while *f0 != l0 && f1 != *l1 {
        reverse_swap_step(&mut l0, &mut f1);
    }
    Pair::new(l0, f1)
}

pub fn reverse_swap_ranges_n<I0, I1, N>(mut l0: I0, mut f1: I1, mut n: N) -> Pair<I0, I1>
where
    I0: Mutable + BidirectionalIterator,
    I1: Mutable<ValueType = I0::ValueType> + ForwardIterator,
    N: Integer,
{
    // Precondition: $\property{mutable\_counted\_range}(l_0-n, n)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, n)$
    while count_down(&mut n) {
        reverse_swap_step(&mut l0, &mut f1);
    }
    Pair::new(l0, f1)
}

//
//  Chapter 10. Rearrangements
//

pub fn cycle_to<I, F>(mut i: I, f: &F)
where
    I: Mutable,
    F: Transformation<Domain = I>,
{
    // Precondition: The orbit of $i$ under $f$ is circular
    // Precondition: $(\forall n \in \mathbb{N})\,\func{deref}(f^n(i))$ is defined
    let mut k = f.call(i.clone());
    while k != i {
        exchange_values(&mut i, &mut k);
        k = f.call(k);
    }
}

// Exercise 10.3: cycle_to variant doing 2n-1 assignments

pub fn cycle_from<I, F>(i: &I, f: &F)
where
    I: Mutable,
    F: Transformation<Domain = I>,
{
    // Precondition: The orbit of $i$ under $f$ is circular
    // Precondition: $(\forall n \in \mathbb{N})\,\func{deref}(f^n(i))$ is defined
    let tmp = i.source().clone();
    let mut j = i.clone();
    let mut k = f.call(i.clone());
    while k != *i {
        *j.sink() = k.source().clone();
        j = k.clone();
        k = f.call(k);
    }
    *j.sink() = tmp;
}

// Exercise 10.4: arbitrary rearrangement using array of n boolean values
// Exercise 10.5: arbitrary rearrangement using total ordering on iterators

pub trait IndexedIterator: ForwardIterator {
    fn rotate_nontrivial(self, m: Self, l: Self) -> Self
    where
        Self: Mutable,
        Self::DistanceType: EuclideanSemiring,
    {
        // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
        rotate_indexed_nontrivial(self, &m, l)
    }
}

pub fn reverse_n_indexed<I>(f: &I, n: I::DistanceType)
where
    I: Mutable + IndexedIterator,
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    let mut i = I::DistanceType::zero();
    let mut n = predecessor(n);
    while i < n {
        // $n = (n_\text{original} - 1) - i$
        exchange_values(&mut f.clone().add(i.clone()), &mut f.clone().add(n.clone()));
        i = successor(i);
        n = predecessor(n);
    }
}

pub fn reverse_bidirectional<I>(mut f: I, mut l: I)
where
    I: Mutable + BidirectionalIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    loop {
        if f == l {
            return;
        }
        l = l.predecessor();
        if f == l {
            return;
        }
        exchange_values(&mut f, &mut l);
        f = f.successor();
    }
}

pub fn reverse_n_bidirectional<I>(f: I, l: I, n: I::DistanceType)
where
    I: Mutable + BidirectionalIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge 0 \leq n \leq l - f$
    reverse_swap_ranges_n(l, f, half_nonnegative(n));
}

pub fn reverse_n_with_buffer<I, B>(f_i: I, n: I::DistanceType, f_b: B) -> I
where
    I: Mutable + ForwardIterator,
    B: Mutable<ValueType = I::ValueType> + BidirectionalIterator,
{
    // Precondition: $\property{mutable\_counted\_range}(f_i, n)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n)$
    reverse_copy(&f_b.clone(), copy_n(f_i.clone(), n, f_b).m1, f_i)
}

pub fn reverse_n_forward<I>(f: I, n: I::DistanceType) -> I
where
    I: Mutable + ForwardIterator,
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    if n < I::DistanceType::two() {
        return f.add(n);
    }
    let h = half_nonnegative(n.clone());
    let n_mod_2 = n - twice(h.clone());
    let m = reverse_n_forward(f.clone(), h.clone()).add(n_mod_2);
    let l = reverse_n_forward(m.clone(), h.clone());
    swap_ranges_n(f, m, h);
    l
}

pub fn reverse_n_adaptive<I, B>(f_i: I, n_i: I::DistanceType, f_b: B, n_b: I::DistanceType) -> I
where
    I: Mutable + ForwardIterator,
    B: Mutable<ValueType = I::ValueType> + BidirectionalIterator,
{
    // Precondition: $\property{mutable\_counted\_range}(f_i, n_i)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_b)$
    if n_i < I::DistanceType::two() {
        return f_i.add(n_i);
    }
    if n_i <= n_b {
        return reverse_n_with_buffer(f_i, n_i, f_b);
    }
    let h_i = half_nonnegative(n_i.clone());
    let n_mod_2 = n_i - twice(h_i.clone());
    let m_i = reverse_n_adaptive(f_i.clone(), h_i.clone(), f_b.clone(), n_b.clone()).add(n_mod_2);
    let l_i = reverse_n_adaptive(m_i.clone(), h_i.clone(), f_b, n_b);
    swap_ranges_n(f_i, m_i, h_i);
    l_i
}

pub trait RandomAccessIterator: IndexedIterator + BidirectionalIterator + TotallyOrdered {
    fn rotate_nontrivial(self, m: Self, l: Self) -> Self
    where
        Self: Mutable,
        Self::DistanceType: EuclideanSemiring,
    {
        // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
        rotate_random_access_nontrivial(self, &m, l)
    }
}

pub struct KRotateFromPermutationRandomAccess<I>
where
    I: RandomAccessIterator,
{
    k: I::DistanceType,
    n_minus_k: I::DistanceType,
    m_prime: I,
}

impl<I> KRotateFromPermutationRandomAccess<I>
where
    I: RandomAccessIterator,
{
    pub fn new(f: I, m: &I, l: I) -> Self {
        // Precondition: $\property{bounded\_range}(f, l) \wedge m \in [f, l)$
        Self {
            k: l.clone().sub(m),
            n_minus_k: m.clone().sub(&f),
            m_prime: f.add(l.sub(m)),
        }
    }
}

impl<I> Transformation for KRotateFromPermutationRandomAccess<I>
where
    I: RandomAccessIterator,
{
    type Domain = I;
    type DistanceType = I::DistanceType;
    fn call(&self, x: Self::Domain) -> Self::Domain {
        // Precondition: $x \in [f, l)$
        if x < self.m_prime {
            x.add(self.n_minus_k.clone())
        } else {
            sub(x, self.k.clone())
        }
    }
}

pub struct KRotateFromPermutationIndexed<I>
where
    I: IndexedIterator,
{
    k: I::DistanceType,
    n_minus_k: I::DistanceType,
    f: I,
}

impl<I> KRotateFromPermutationIndexed<I>
where
    I: IndexedIterator,
{
    pub fn new(f: I, m: I, l: I) -> Self {
        // Precondition: $\property{bounded\_range}(f, l) \wedge m \in [f, l)$
        Self {
            k: l.sub(&m),
            n_minus_k: m.sub(&f),
            f,
        }
    }
}

impl<I> Transformation for KRotateFromPermutationIndexed<I>
where
    I: IndexedIterator,
{
    type Domain = I;
    type DistanceType = I::DistanceType;
    fn call(&self, x: Self::Domain) -> Self::Domain {
        // Precondition: $x \in [f, l)$
        let i = x.clone().sub(&self.f);
        if i < self.k {
            x.add(self.n_minus_k.clone())
        } else {
            self.f.clone().add(i - self.k.clone())
        }
    }
}

pub fn rotate_cycles<I, F>(f: I, m: &I, l: I, from: &F) -> I
where
    I: Mutable + IndexedIterator,
    I::DistanceType: EuclideanSemiring,
    F: Transformation<Domain = I>,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge m \in [f, l]$
    // Precondition: $from$ is a from-permutation on $[f, l)$
    let mut d = gcd(m.clone().sub(&f), l.clone().sub(m));
    while count_down(&mut d) {
        cycle_from(&f.clone().add(d.clone()), from);
    }
    f.add(l.sub(m))
}

pub fn rotate_indexed_nontrivial<I>(f: I, m: &I, l: I) -> I
where
    I: Mutable + IndexedIterator,
    I::DistanceType: EuclideanSemiring,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    let p = KRotateFromPermutationIndexed::new(f.clone(), m.clone(), l.clone());
    rotate_cycles(f, m, l, &p)
}

pub fn rotate_random_access_nontrivial<I>(f: I, m: &I, l: I) -> I
where
    I: Mutable + RandomAccessIterator,
    I::DistanceType: EuclideanSemiring,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    let p = KRotateFromPermutationRandomAccess::new(f.clone(), m, l.clone());
    rotate_cycles(f, m, l, &p)
}

pub fn rotate_bidirectional_nontrivial<I>(f: I, m: &I, l: I) -> I
where
    I: Mutable + BidirectionalIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    reverse_bidirectional(f.clone(), m.clone());
    reverse_bidirectional(m.clone(), l.clone());
    let p = reverse_swap_ranges_bounded(m, l, f, m);
    reverse_bidirectional(p.m1.clone(), p.m0.clone());
    if *m == p.m0 {
        p.m1
    } else {
        p.m0
    }
}

pub fn rotate_forward_annotated<I>(mut f: I, mut m: I, l: &I)
where
    I: Mutable + ForwardIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    let mut a = m.clone().sub(&f);
    let mut b = l.clone().sub(&m);
    loop {
        let p = swap_ranges_bounded(f, &m, m.clone(), l);
        if p.m0 == m && p.m1 == *l {
            assert(a == b);
            return;
        }
        f = p.m0;
        if f == m {
            assert(b > a);
            m = p.m1;
            b = b - a.clone();
        } else {
            assert(a > b);
            a = a - b.clone();
        }
    }
}

pub fn rotate_forward_step<I>(f: &mut I, m: &mut I, l: &I)
where
    I: Mutable + ForwardIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    let mut c = m.clone();
    loop {
        swap_step(f, &mut c);
        if f == m {
            *m = c.clone();
        }
        if c == *l {
            break;
        }
    }
}

pub fn rotate_forward_nontrivial<I>(mut f: I, mut m: I, l: &I) -> I
where
    I: Mutable + ForwardIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    rotate_forward_step(&mut f, &mut m, l);
    let m_prime = f.clone();
    while m != *l {
        rotate_forward_step(&mut f, &mut m, l);
    }
    m_prime
}

pub fn rotate_partial_nontrivial<I>(f: I, m: I, l: &I) -> I
where
    I: Mutable + ForwardIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    swap_ranges(m, l, f)
}

// swap_ranges_backward
// rotate_partial_backward_nontrivial

pub fn rotate_with_buffer_nontrivial<I, B>(f: I, m: I, l: &I, f_b: B) -> I
where
    I: Mutable + ForwardIterator,
    B: Mutable<ValueType = I::ValueType> + ForwardIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    // Precondition: $\property{mutable\_counted\_range}(f_b, l-f)$
    let l_b = copy(f.clone(), &m, f_b.clone());
    let m_prime = copy(m, l, f);
    copy(f_b, &l_b, m_prime.clone());
    m_prime
}

pub fn rotate_with_buffer_backward_nontrivial<I, B>(f: I, m: I, l: I, f_b: B) -> I
where
    I: Mutable + BidirectionalIterator,
    B: Mutable<ValueType = I::ValueType> + ForwardIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    // Precondition: $\property{mutable\_counted\_range}(f_b, l-f)$
    let l_b = copy(m.clone(), &l, f_b.clone());
    copy_backward(&f, m, l);
    copy(f_b, &l_b, f)
}

// Section 10.5. Algorithm selection

pub fn reverse_indexed<I>(f: &I, l: I)
where
    I: Mutable + IndexedIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    reverse_n_indexed(f, l.sub(f));
}

pub trait ConstructAll<I>
where
    I: Writable + ForwardIterator,
{
    fn construct_all(f: I, l: &I);
}

impl<I> ConstructAll<I> for True
where
    I: Writable + ForwardIterator,
{
    fn construct_all(mut f: I, l: &I) {
        // Precondition:
        // $(\forall i \in [f, l)) \func{sink}(i) \text{refers to raw memory, not an object}$
        // Postcondition:
        // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
        // We assume if an iterator is writeable, its value can be constructed
        while f != *l {
            //construct(f.sink());
            f = f.successor();
        }
    }
}

impl<I> ConstructAll<I> for False
where
    I: Writable + ForwardIterator,
{
    fn construct_all(_: I, _: &I) {
        // Precondition:
        // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
        // Postcondition:
        // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    }
}

/*
// temporary_buffer type

template<typename I>
    requires(Writeable(I) && ForwardIterator(I))
void construct_all(I f, I l)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{refers to raw memory, not an object}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a default-constructed state}$
    // We assume if an iterator is writeable, its value can be constructed
    construct_all(f, l, NeedsConstruction(ValueType(I))());
}

template<typename I>
    requires(Writeable(I) && ForwardIterator(I))
void construct_all(I f, I l, true_type)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{refers to raw memory, not an object}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // We assume if an iterator is writeable, its value can be constructed
    while (f != l) {
        construct(sink(f));
        f = successor(f);
    }
}

template<typename I>
    requires(Writeable(I) && ForwardIterator(I) &&
        NeedsConstruction(ValueType(I)) == false_type)
void construct_all(I /*f*/, I /*l*/, false_type)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
}

template<typename I>
    requires(Writeable(I) && ForwardIterator(I))
void destroy_all(I f, I l)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{refers to raw memory, not an object}$
    // We assume if an iterator is writeable, its value can be destroyed
    destroy_all(f, l, NeedsDestruction(ValueType(I))());
}

template<typename I>
    requires(Writeable(I) && ForwardIterator(I))
void destroy_all(I f, I l, true_type)
{
    // Precondition: $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // Postcondition: $(\forall i \in [f, l)) \func{sink}(i) \text{refers to raw memory, not an object}$
    // We assume if an iterator is writeable, its value can be destroyed
    while (f != l) {
        destroy(sink(f));
        f = successor(f);
    }
}

template<typename I>
    requires(Writeable(I) && ForwardIterator(I) &&
        NeedsDestruction(ValueType(I)) == false_type)
void destroy_all(I /*f*/, I /*l*/, false_type)
{
    // Precondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
    // Postcondition:
    // $(\forall i \in [f, l)) \func{sink}(i) \text{is in a partially-formed state}$
}
*/

// NeedsConstruction and NeedsDestruction should be overloaded for every POD type

struct Unique<T> {
    ptr: *const T,           // *const for variance
    _marker: PhantomData<T>, // For the drop checker
}

pub struct TemporaryBuffer<T>
where
    T: Regular,
{
    p: Unique<T>,
    n: <Pointer<T> as Iterator>::DistanceType,
}

use std::alloc::{alloc, dealloc, Layout};
use std::mem::{align_of, size_of};

impl<T> TemporaryBuffer<T>
where
    T: Regular,
{
    #[must_use]
    pub fn new(mut n: <Pointer<T> as Iterator>::DistanceType) -> Self {
        let (elem_size, align) = (size_of::<T>(), align_of::<T>());
        loop {
            unsafe {
                let p = alloc(Layout::from_size_align(elem_size * n, align).unwrap()) as *mut T;
                if !p.is_null() {
                    for i in 0..n {
                        std::ptr::write(p.add(i), T::default());
                    }
                    return Self {
                        p: Unique {
                            ptr: p,
                            _marker: PhantomData,
                        },
                        n,
                    };
                }
            }
            n = half_nonnegative(n);
        }
    }
    #[must_use]
    pub fn size(&self) -> <Pointer<T> as Iterator>::DistanceType {
        self.n
    }
    #[must_use]
    pub fn begin(&self) -> Pointer<T> {
        Pointer::new(self.p.ptr as *mut T)
    }
}

impl<T> Drop for TemporaryBuffer<T>
where
    T: Regular,
{
    fn drop(&mut self) {
        unsafe {
            for i in 0..self.n {
                std::ptr::read(self.p.ptr.add(i));
            }
            dealloc(
                self.p.ptr as *mut u8,
                Layout::from_size_align(size_of::<T>() * self.n, align_of::<T>()).unwrap(),
            );
        }
    }
}

/*
private:
    // We use private only to signal lack of regularity of a type
    temporary_buffer(const temporary_buffer&) { }
    void operator=(const temporary_buffer&) { }
};

template<typename T>
    requires(Regular(T))
DistanceType(pointer(T)) size(const temporary_buffer<T>& b)
{
    return b.n;
}

template<typename T>
    requires(Regular(T))
pointer(T) begin(temporary_buffer<T>& b)
{
    return b.p;
}
*/

#[derive(Clone, Eq, PartialEq)]
pub struct Pointer<T>(*mut T);

impl<T> Pointer<T> {
    fn new(x: *mut T) -> Self {
        Self(x)
    }
}

impl<T> Default for Pointer<T> {
    #[must_use]
    fn default() -> Self {
        Self(std::ptr::null_mut())
    }
}

impl<T> Reference for Pointer<T>
where
    T: Regular,
{
    type ValueType = T;
}

impl<T> Readable for Pointer<T>
where
    T: Regular,
{
    #[must_use]
    fn source(&self) -> &Self::ValueType {
        unsafe { self.0.as_ref().unwrap() }
    }
}

impl<T> Writable for Pointer<T>
where
    T: Regular,
{
    fn sink(&mut self) -> &mut Self::ValueType {
        unsafe { self.0.as_mut().unwrap() }
    }
}

impl<T> Mutable for Pointer<T> where T: Regular {}

impl<T> Iterator for Pointer<T>
where
    T: Regular,
{
    type DistanceType = usize;
    #[must_use]
    fn successor(&self) -> Self {
        unsafe { Pointer::new(self.0.offset(1)) }
    }
}

impl<T> BidirectionalIterator for Pointer<T>
where
    T: Regular,
{
    #[must_use]
    fn predecessor(&self) -> Self {
        unsafe { Pointer::new(self.0.offset(-1)) }
    }
}

pub fn reverse_n_with_temporary_buffer<I>(f: I, n: I::DistanceType)
where
    I: Mutable + ForwardIterator,
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    let b = TemporaryBuffer::new(NumCast::from(n.clone()).unwrap());
    reverse_n_adaptive(f, n, b.begin(), NumCast::from(b.size()).unwrap());
}

pub fn rotate<I>(f: I, m: I, l: I) -> I
where
    I: Mutable + ForwardIterator,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge m \in [f, l]$
    if m == f {
        return l;
    }
    if m == l {
        return f;
    }
    f.rotate_nontrivial(m, l)
}

//
//  Chapter 11. Partition and merging
//

// Exercise 11.1:

pub fn partitioned_at_point<I, P>(f: I, m: I, l: &I, p: &P) -> bool
where
    I: Readable + Iterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{readable\_bounded\_range}(f, l) \wedge m \in [f, l]$
    none(f, &m, p) && all(m, l, p)
}

// Exercise 11.2:

pub fn potential_partition_point<I, P>(f: I, l: &I, p: &P) -> I
where
    I: Readable + ForwardIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    count_if_not(f.clone(), l, p, f)
}

pub fn partition_semistable<I, P>(f: I, l: &I, p: &P) -> I
where
    I: Mutable + ForwardIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    let mut i = find_if(f, l, p);
    if i == *l {
        return i;
    }
    let mut j = i.successor();
    loop {
        j = find_if_not(j, l, p);
        if j == *l {
            return i;
        }
        swap_step(&mut i, &mut j);
    }
}

// Exercise 11.3: rewrite partition_semistable, expanding find_if_not inline and
// eliminating extra test against l

// Exercise 11.4: substitute copy_step(j, i) for swap_step(i, j) in partition_semistable

pub fn remove_if<I, P>(f: I, l: &I, p: &P) -> I
where
    I: Mutable + ForwardIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    let mut i = find_if(f, l, p);
    if i == *l {
        return i;
    }
    let mut j = i.successor();
    loop {
        j = find_if_not(j, l, p);
        if j == *l {
            return i;
        }
        copy_step(&mut j, &mut i);
    }
}

// Exercise 11.5:

//template<typename I, typename P>
//    requires(Mutable(I) && ForwardIterator(I) &&
//        UnaryPredicate(P) && ValueType(I) == Domain(P))
//void partition_semistable_omit_last_predicate_evaluation(I f, I l, P p)
//{
//    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
//    ...
//}

pub fn partition_bidirectional<I, P>(mut f: I, mut l: I, p: &P) -> I
where
    I: Mutable + BidirectionalIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    loop {
        f = find_if(f, &l, p);
        l = find_backward_if_not(&f, l, p);
        if f == l {
            return f;
        }
        reverse_swap_step(&mut l, &mut f);
    }
}

// Exercise 11.6:

pub fn partition_forward<I, P>(mut f: I, l: &I, p: &P) -> I
where
    I: Mutable + ForwardIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    let i = count_if_not(f.clone(), l, p, f.clone());
    let mut j = i.clone();
    loop {
        j = find_if_not(j, l, p);
        if j == *l {
            return i;
        }
        f = find_if_unguarded(f, p);
        swap_step(&mut f, &mut j);
    }
}

// Exercise 11.7: partition_single_cycle

pub fn partition_single_cycle<I, P>(mut f: I, mut l: I, p: &P) -> I
where
    I: Mutable + BidirectionalIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    f = find_if(f, &l, p);
    l = find_backward_if_not(&f, l, p);
    if f == l {
        return f;
    }
    l = l.predecessor();
    let tmp = f.source().clone();
    loop {
        *f.sink() = l.source().clone();
        f = find_if(f.successor(), &l, p);
        if f == l {
            *l.sink() = tmp;
            return f;
        }
        *l.sink() = f.source().clone();
        l = find_backward_if_not_unguarded(l, p);
    }
}

// Exercise 11.8: partition_sentinel

pub fn partition_bidirectional_unguarded<I, P>(mut f: I, mut l: I, p: &P) -> I
where
    I: Mutable + BidirectionalIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition:
    // $(\neg \func{all}(f, l, p) \wedge \func{some}(f, l, p)) \vee
    // (\neg p(\func{source}(f-1)) \wedge p(\func{source}(l)))$
    loop {
        f = find_if_unguarded(f, p);
        l = find_backward_if_not_unguarded(l, p);
        if l.successor() == f {
            return f;
        }
        exchange_values(&mut f, &mut l);
        f = f.successor(); // $\neg p(\func{source}(f-1)) \wedge p(\func{source}(l))$
    }
}

pub fn partition_sentinel<I, P>(mut f: I, mut l: I, p: &P) -> I
where
    I: Mutable + BidirectionalIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    f = find_if(f, &l, p);
    l = find_backward_if_not(&f, l, p);
    if f == l {
        return f;
    }
    l = l.predecessor();
    exchange_values(&mut f, &mut l);
    f = f.successor();
    partition_bidirectional_unguarded(f, l, p)
}

// Exercise 11.9: partition_single_cycle_sentinel

pub fn partition_indexed<I, P>(f: I, l: I, p: &P) -> I
where
    I: Mutable + IndexedIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    let mut i = I::DistanceType::zero();
    let mut j = l.sub(&f);
    loop {
        loop {
            if i == j {
                return f.add(i);
            }
            if p.call(f.clone().add(i.clone()).source()) {
                break;
            }
            i = successor(i);
        }
        loop {
            j = predecessor(j);
            if i == j {
                return f.add(j).add(I::DistanceType::one());
            }
            if !p.call(f.clone().add(j.clone()).source()) {
                break;
            }
        }
        exchange_values(&mut f.clone().add(i.clone()), &mut f.clone().add(j.clone()));
        i = successor(i);
    }
}

pub fn partition_stable_with_buffer<I, B, P>(f: I, l: &I, f_b: B, p: P) -> I
where
    I: Mutable + ForwardIterator,
    B: Mutable<ValueType = I::ValueType> + ForwardIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, l-f)$
    let x = partition_copy(f.clone(), l, f, f_b.clone(), p);
    copy(f_b, &x.m1, x.m0.clone());
    x.m0
}

pub fn partition_stable_singleton<I, P>(mut f: I, p: &P) -> Pair<I, I>
where
    I: Mutable + ForwardIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{readable\_bounded\_range}(f, \func{successor}(f))$
    let l = f.successor();
    if !p.call(f.source()) {
        f = l.clone();
    }
    Pair::new(f, l)
}

#[derive(Clone, Default, Eq, PartialEq)]
pub struct CombineRanges<I>(PhantomData<I>);

impl<I> BinaryOperation for CombineRanges<I>
where
    I: Mutable + ForwardIterator,
{
    type Domain = Pair<I, I>;
    fn call(&self, x: &Self::Domain, y: &Self::Domain) -> Self::Domain {
        // Precondition: $\property{mutable\_bounded\_range}(x.m0, y.m0)$
        // Precondition: $x.m1 \in [x.m0, y.m0]$
        Pair::new(
            rotate(x.m0.clone(), x.m1.clone(), y.m0.clone()),
            y.m1.clone(),
        )
    }
}

pub fn partition_stable_n_nonempty<I, P>(f: I, n: I::DistanceType, p: &P) -> Pair<I, I>
where
    I: Mutable + ForwardIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{mutable\_counted\_range}(f, n) \wedge n > 0$
    if one(&n) {
        return partition_stable_singleton(f, p);
    }
    let h = half_nonnegative(n.clone());
    let x = partition_stable_n_nonempty(f, h.clone(), p);
    let y = partition_stable_n_nonempty(x.m1.clone(), n - h, p);
    CombineRanges::default().call(&x, &y)
}

pub fn partition_stable_n<I, P>(f: I, n: I::DistanceType, p: &P) -> Pair<I, I>
where
    I: Mutable + ForwardIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    if zero(&n) {
        return Pair::new(f.clone(), f);
    }
    partition_stable_n_nonempty(f, n, p)
}

// Exercise 11.10: partition_stable_n_adaptive

pub fn partition_stable<I, P>(f: I, l: I, p: &P) -> I
where
    I: Mutable + ForwardIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    let n = l.sub(&f);
    partition_stable_n(f, n, p).m0
}

pub struct PartitionTrivial<I, P> {
    p: P,
    _marker: PhantomData<I>,
}

impl<I, P> PartitionTrivial<I, P> {
    pub fn new(p: P) -> Self {
        Self {
            p,
            _marker: PhantomData,
        }
    }
}

impl<I, P> FunctionalProcedure for PartitionTrivial<I, P>
where
    I: Regular,
{
    type Codomain = Pair<I, I>;
}

impl<I, P> UnaryFunction for PartitionTrivial<I, P>
where
    I: Mutable + ForwardIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    type Domain = I;
    fn call(&self, i: &Self::Domain) -> Self::Codomain {
        partition_stable_singleton(i.clone(), &self.p)
    }
}

pub fn add_to_counter<I, Op>(
    mut f: I,
    l: &I,
    op: &Op,
    mut x: Op::Domain,
    z: Op::Domain,
) -> Op::Domain
where
    I: Mutable + ForwardIterator,
    Op: BinaryOperation<Domain = I::ValueType>,
{
    if x == z {
        return z;
    }
    while f != *l {
        if *f.source() == z {
            *f.sink() = x;
            return z;
        }
        x = op.call(f.source(), &x);
        *f.sink() = z.clone();
        f = f.successor();
    }
    x
}

pub struct CounterMachine<Op>
where
    Op: BinaryOperation,
{
    op: Op,
    z: Op::Domain,
    f: [Op::Domain; 64],
    n: <Pointer<Op::Domain> as Iterator>::DistanceType,
}

impl<Op> CounterMachine<Op>
where
    Op: BinaryOperation,
{
    pub fn new(op: Op, z: Op::Domain) -> Self {
        Self {
            op,
            z,
            f: [
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
                Op::Domain::default(),
            ],
            n: <Pointer<Op::Domain> as Iterator>::DistanceType::zero(),
        }
    }
}

impl<Op> CounterMachine<Op>
where
    Op: BinaryOperation,
{
    pub fn call(&mut self, x: Op::Domain) {
        // Precondition: must not be called more than $2^{64}-1$ times
        let tmp = add_to_counter(
            Pointer::new(&mut self.f[0]),
            &Pointer::new(&mut self.f[self.n]),
            &self.op,
            x,
            self.z.clone(),
        );
        if tmp != self.z {
            *(Pointer::new(&mut self.f[self.n])).sink() = tmp;
            self.n = successor(self.n);
        }
    }
}

#[derive(Clone, Default, Eq, PartialEq)]
pub struct TransposeOperation<Op> {
    op: Op,
}

impl<Op> TransposeOperation<Op> {
    pub fn new(op: Op) -> Self {
        Self { op }
    }
}

impl<Op> BinaryOperation for TransposeOperation<Op>
where
    Op: BinaryOperation,
{
    type Domain = Op::Domain;
    fn call(&self, x: &Op::Domain, y: &Op::Domain) -> Op::Domain {
        self.op.call(y, x)
    }
}

pub trait FunctionalProcedure {
    type Codomain;
}

pub trait UnaryFunction: FunctionalProcedure {
    type Domain;
    fn call(&self, x: &Self::Domain) -> Self::Codomain;
}

pub fn reduce_balanced<I, Op, F>(mut f: I, l: &I, op: Op, fun: &F, z: &Op::Domain) -> Op::Domain
where
    I: Iterator,
    Op: BinaryOperation,
    F: UnaryFunction<Domain = I, Codomain = Op::Domain>,
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge l - f < 2^{64}$
    // Precondition: $\property{partially\_associative}(op)$
    // Precondition: $(\forall x \in [f, l))\,fun(x)$ is defined
    let mut c = CounterMachine::new(op.clone(), z.clone());
    while f != *l {
        c.call(fun.call(&f));
        f = f.successor();
    }
    let t_op = TransposeOperation::new(op);
    let f = Pointer::new(c.f.as_mut_ptr());
    reduce_nonzeroes_1(f.clone(), &f.add(c.n), &t_op, &z)
}

pub fn reduce_balanced_1<I, Op>(mut f: I, l: &I, op: Op, z: &Op::Domain) -> Op::Domain
where
    I: ReadableIterator,
    Op: BinaryOperation<Domain = I::ValueType>,
{
    // Precondition: $\property{readable\_bounded\_range}(f, l) \wedge l-f < 2^{33}$
    // Precondition: $\property{partially\_associative}(op)$
    let mut c = CounterMachine::new(op.clone(), z.clone());
    while f != *l {
        c.call(f.source().clone());
        f = f.successor();
    }
    let t_op = TransposeOperation::new(op);
    let f = Pointer::new(c.f.as_mut_ptr());
    reduce_nonzeroes_1(f.clone(), &f.add(c.n), &t_op, z)
}

pub fn partition_stable_iterative<I, P>(f: I, l: &I, p: P) -> I
where
    I: Mutable + ForwardIterator,
    P: UnaryPredicate<Domain = I::ValueType>,
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge l - f < 2^{64}$
    reduce_balanced(
        f.clone(),
        l,
        CombineRanges::default(),
        &PartitionTrivial::new(p),
        &Pair::new(f.clone(), f),
    )
    .m0
}

pub fn merge_n_with_buffer<I, B, R>(
    f0: I,
    n0: I::DistanceType,
    f1: I,
    n1: I::DistanceType,
    f_b: B,
    r: R,
) -> I
where
    I: Mutable + ForwardIterator,
    B: Mutable<ValueType = I::ValueType> + ForwardIterator,
    R: Relation<Domain = I::ValueType>,
{
    // Precondition: $\func{mergeable}(f_0, n_0, f_1, n_1, r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_0)$
    copy_n(f0.clone(), n0.clone(), f_b.clone());
    merge_copy_n(f_b, NumCast::from(n0).unwrap(), f1, n1, f0, r).m2
}

pub fn sort_n_with_buffer<I, B, R>(f: I, n: I::DistanceType, f_b: B, r: R) -> I
where
    I: Mutable + ForwardIterator,
    B: Mutable<ValueType = I::ValueType> + ForwardIterator,
    R: Relation<Domain = I::ValueType>,
{
    // Property:
    // $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, \lceil n/2 \rceil)$
    let h = half_nonnegative(n.clone());
    if zero(&h) {
        return f.add(n);
    }
    let m = sort_n_with_buffer(f.clone(), h.clone(), f_b.clone(), r.clone());
    sort_n_with_buffer(m.clone(), n.clone() - h.clone(), f_b.clone(), r.clone());
    merge_n_with_buffer(f, h.clone(), m, n - h, f_b, r)
}

pub fn merge_n_step_0<I, R>(
    f0: I,
    n0: I::DistanceType,
    f1: I,
    n1: I::DistanceType,
    r: &R,
    f0_0: &mut I,
    n_0_0: &mut I::DistanceType,
    f0_1: &mut I,
    n_0_1: &mut I::DistanceType,
    f1_0: &mut I,
    n_1_0: &mut I::DistanceType,
    f1_1: &mut I,
    n_1_1: &mut I::DistanceType,
) where
    I: Mutable + ForwardIterator,
    R: Relation<Domain = I::ValueType>,
{
    // Precondition: $\property{mergeable}(f_0, n_0, f_1, n_1, r)$
    *f0_0 = f0;
    *n_0_0 = half_nonnegative(n0.clone());
    *f0_1 = f0_0.clone().add(n_0_0.clone());
    *f1_1 = lower_bound_n(f1.clone(), n1.clone(), f0_1.source(), r);
    *f1_0 = rotate(f0_1.clone(), f1, f1_1.clone());
    *n_0_1 = f1_0.clone().sub(f0_1);
    *f1_0 = f1_0.successor();
    *n_1_0 = predecessor(n0 - n_0_0.clone());
    *n_1_1 = n1 - n_0_1.clone();
}

pub fn merge_n_step_1<I, R>(
    f0: I,
    n0: I::DistanceType,
    f1: I,
    n1: I::DistanceType,
    r: &R,
    f0_0: &mut I,
    n_0_0: &mut I::DistanceType,
    f0_1: &mut I,
    n_0_1: &mut I::DistanceType,
    f1_0: &mut I,
    n_1_0: &mut I::DistanceType,
    f1_1: &mut I,
    n_1_1: &mut I::DistanceType,
) where
    I: Mutable + ForwardIterator,
    R: Relation<Domain = I::ValueType>,
{
    // Precondition: $\property{mergeable}(f_0, n_0, f_1, n_1, r)$
    *f0_0 = f0.clone();
    *n_0_1 = half_nonnegative(n1.clone());
    *f1_1 = f1.clone().add(n_0_1.clone());
    *f0_1 = upper_bound_n(f0, n0.clone(), f1_1.source(), r);
    *f1_1 = f1_1.successor();
    *f1_0 = rotate(f0_1.clone(), f1, f1_1.clone());
    *n_0_0 = f0_1.clone().sub(f0_0);
    *n_1_0 = n0 - n_0_0.clone();
    *n_1_1 = predecessor(n1 - n_0_1.clone());
}

pub fn merge_n_adaptive<I, B, R>(
    f0: I,
    n0: I::DistanceType,
    f1: I,
    n1: I::DistanceType,
    f_b: B,
    n_b: B::DistanceType,
    r: R,
) -> I
where
    I: Mutable + ForwardIterator,
    B: Mutable<ValueType = I::ValueType> + ForwardIterator,
    R: Relation<Domain = I::ValueType>,
{
    // Precondition: $\property{mergeable}(f_0, n_0, f_1, n_1, r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_b)$
    if zero(&n0) || zero(&n1) {
        return f0.add(n0).add(n1);
    }
    if n0 <= NumCast::from(n_b.clone()).unwrap() {
        return merge_n_with_buffer(f0, n0, f1, n1, f_b, r);
    }
    let mut f0_0 = I::default();
    let mut f0_1 = I::default();
    let mut f1_0 = I::default();
    let mut f1_1 = I::default();
    let mut n_0_0 = I::DistanceType::default();
    let mut n_0_1 = I::DistanceType::default();
    let mut n_1_0 = I::DistanceType::default();
    let mut n_1_1 = I::DistanceType::default();
    if n0 < n1 {
        merge_n_step_0(
            f0, n0, f1, n1, &r, &mut f0_0, &mut n_0_0, &mut f0_1, &mut n_0_1, &mut f1_0,
            &mut n_1_0, &mut f1_1, &mut n_1_1,
        );
    } else {
        merge_n_step_1(
            f0, n0, f1, n1, &r, &mut f0_0, &mut n_0_0, &mut f0_1, &mut n_0_1, &mut f1_0,
            &mut n_1_0, &mut f1_1, &mut n_1_1,
        );
    }
    merge_n_adaptive(
        f0_0,
        n_0_0,
        f0_1,
        n_0_1,
        f_b.clone(),
        n_b.clone(),
        r.clone(),
    );
    merge_n_adaptive(f1_0, n_1_0, f1_1, n_1_1, f_b, n_b, r)
}

pub fn sort_n_adaptive<I, B, R>(f: I, n: I::DistanceType, f_b: B, n_b: B::DistanceType, r: R) -> I
where
    I: Mutable + ForwardIterator,
    B: Mutable<ValueType = I::ValueType> + ForwardIterator,
    R: Relation<Domain = I::ValueType>,
{
    // Precondition:
    // $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_b)$
    let h = half_nonnegative(n.clone());
    if zero(&h) {
        return f.add(n);
    }
    let m = sort_n_adaptive(f.clone(), h.clone(), f_b.clone(), n_b.clone(), r.clone());
    sort_n_adaptive(
        m.clone(),
        n.clone() - h.clone(),
        f_b.clone(),
        n_b.clone(),
        r.clone(),
    );
    merge_n_adaptive(f, h.clone(), m, n - h, f_b, n_b, r)
}

pub fn sort_n<I, R>(f: I, n: &I::DistanceType, r: R) -> I
where
    I: Mutable + ForwardIterator,
    R: Relation<Domain = I::ValueType>,
{
    // Precondition:
    // $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    let b = TemporaryBuffer::new(NumCast::from(half_nonnegative(n.clone())).unwrap());
    sort_n_adaptive(f, n.clone(), b.begin(), b.size(), r)
}

/*
//
//  Chapter 12. Composite objects
//


// pair type: see Chapter 1 of this file


// Exercise 12.1: less< pair<T0, T1> > using less<T0> and less<T1>


// triple type: see Chapter 1 of this file


// Exercise 12.2: triple type


// array_k type

template<int k, typename T>
    requires(0 < k && k <= MaximumValue(int) / sizeof(T) &&
        Regular(T))
struct array_k
{
    T a[k];
    T& operator[](int i)
    {
        // Precondition: $0 \leq i < \func{size}(x)$
        return a[i];
    }
};

template<int k, typename T>
    requires(Regular(T))
struct size_value< array_k<k, T> >
{
    static const int value = k;
};

template<int k, typename T>
    requires(Regular(T))
struct iterator_type< array_k<k, T> >
{
    typedef pointer(T) type;
};

template<int k, typename T>
    requires(Regular(T))
struct value_type< array_k<k, T> >
{
    typedef T type;
};

template<int k, typename T>
    requires(Regular(T))
struct size_type< array_k<k, T> >
{
    typedef DistanceType(pointer(T)) type;
};

template<int k, typename T>
    requires(0 < k && k <= MaximumValue(int) / sizeof(T) &&
        Regular(T))
struct underlying_type< array_k<k, T> >
{
    typedef array_k<k, UnderlyingType(T)> type;
};

template<int k, typename T>
    requires(Regular(T))
pointer(T) begin(array_k<k, T>& x)
{
    return addressof(x.a[0]);
}

template<int k, typename T>
    requires(Regular(T))
const pointer(T) begin(const array_k<k, T>& x)
{
    return addressof(x.a[0]);
}

template<int k, typename T>
    requires(Regular(T))
pointer(T) end(array_k<k, T>& x)
{
    return begin(x) + k;
}

template<int k, typename T>
    requires(Regular(T))
const pointer(T) end(const array_k<k, T>& x)
{
    return begin(x) + k;
}

template<int k, typename T>
    requires(Regular(T))
bool operator==(const array_k<k, T>& x, const array_k<k, T>& y)
{
    return lexicographical_equal(begin(x), end(x),
                                 begin(y), end(y));
}

template<int k, typename T>
    requires(Regular(T))
bool operator<(const array_k<k, T>& x, const array_k<k, T>& y)
{
    return lexicographical_less(begin(x), end(x),
                                begin(y), end(y));
}

template<int k, typename T>
    requires(Regular(T))
int size(const array_k<k, T>&) // unused parameter name dropped to avoid warning
{
    return k;
}

template<int k, typename T>
    requires(Regular(T))
bool empty(const array_k<k, T>&) // unused parameter name dropped to avoid warning
{
    return false;
}


// concept Linearizeable

//  Since we already defined ValueType for any (regular) T,
//  C++ will not let us define it for any linearizable T like this:

// template<typename W>
//     requires(Linearizable(W))
// struct value_type
// {
//     typedef ValueType(IteratorType(W)) type;
// };

// Instead, each type W that models Linearizable must provide
//      the corresponding specialization of value_type

template<typename W>
    requires(Linearizable(W))
bool linearizable_equal(const W& x, const W& y)
{
    return lexicographical_equal(begin(x), end(x), begin(y), end(y));
}

template<typename W>
    requires(Linearizable(W))
bool linearizable_ordering(const W& x, const W& y)
{
    return lexicographical_less(begin(x), end(x), begin(y), end(y));
}

template<typename W>
    requires(Linearizeable(W))
DistanceType(IteratorType(W)) size(const W& x)
{
    return end(x) - begin(x);
}

template<typename W>
    requires(Linearizeable(W))
bool empty(const W& x)
{
    return begin(x) == end(x);
}


// type bounded_range
// model Linearizable(bounded_range)

template<typename I>
    requires(Readable(I) && Iterator(I))
struct bounded_range {
    I f;
    I l;
    bounded_range() { }
    bounded_range(const I& f, const I& l) : f(f), l(l) { }
    const ValueType(I)& operator[](DistanceType(I) i)
    {
        // Precondition: $0 \leq i < l - f$
        return source(f + i);
    }
};

template<typename I>
    requires(Readable(I) && Iterator(I))
struct iterator_type< bounded_range<I> >
{
    typedef I type;
};

template<typename I>
    requires(Readable(I) && Iterator(I))
struct value_type< bounded_range<I> >
{
    typedef ValueType(I) type;
};

template<typename I>
    requires(Readable(I) && Iterator(I))
struct size_type< bounded_range<I> >
{
    typedef DistanceType(I) type;
};

template<typename I>
    requires(Readable(I) && Iterator(I))
I begin(const bounded_range<I>& x) { return x.f; }

template<typename I>
    requires(Readable(I) && Iterator(I))
I end(const bounded_range<I>& x) { return x.l; }

template<typename I>
    requires(Readable(I) && Iterator(I))
bool operator==(const bounded_range<I>& x,
                const bounded_range<I>& y)
{
    return begin(x) == begin(y) && end(x) == end(y);
}

template<typename I>
    requires(Readable(I) && Iterator(I))
struct less< bounded_range<I> >
{
    bool operator()(const bounded_range<I>& x,
                    const bounded_range<I>& y)
    {
        less<I> less_I;
        return less_I(begin(x), begin(y)) ||
               (!less_I(begin(y), begin(x)) &&
                 less_I(end(x), end(y)));
    }
};


// type counted_range
// model Linearizable(counted_range)

template<typename I>
    requires(Readable(I) && Iterator(I)) // should it be ForwardIterator?
struct counted_range {
    typedef DistanceType(I) N;
    I f;
    N n;
    counted_range() { }
    counted_range(I f, N n) : f(f), n(n) { }
    const ValueType(I)& operator[](int i)
    {
        // Precondition: $0 \leq i < l - f$
        return source(f + i);
    }
};

template<typename I>
    requires(Readable(I) && Iterator(I))
struct iterator_type< counted_range<I> >
{
    typedef I type;
};

template<typename I>
    requires(Readable(I) && Iterator(I))
struct value_type< counted_range<I> >
{
    typedef ValueType(I) type;
};

template<typename I>
    requires(Readable(I) && Iterator(I))
struct size_type< counted_range<I> >
{
    typedef DistanceType(I) type;
};


template<typename I>
    requires(Readable(I) && Iterator(I))
I begin(const counted_range<I>& x) { return x.f; }

template<typename I>
    requires(Readable(I) && Iterator(I))
I end(const counted_range<I>& x) { return x.f + x.n; }

template<typename I>
    requires(Readable(I) && Iterator(I))
DistanceType(I) size(const counted_range<I>& x) { return x.n; }

template<typename I>
    requires(Readable(I) && Iterator(I))
bool empty(counted_range<I>& x) { return size(x) == 0; }

template<typename I>
    requires(Readable(I) && Iterator(I))
bool operator==(const counted_range<I>& x,
                const counted_range<I>& y)
{
    return begin(x) == begin(y) && size(x) == size(y);
}

template<typename I>
    requires(Readable(I) && Iterator(I))
struct less< counted_range<I> >
{
    bool operator()(const counted_range<I>& x,
                    const counted_range<I>& y)
    {
        less<I> less_I;
        return less_I(begin(x), begin(y)) ||
               (!less_I(begin(y), begin(x)) &&
                 size(x) < size(y));
    }
};


// concept Position(T) means
//     BaseType : Position -> Linearizable
//  /\ IteratorType : Position -> Iterator
//  /\ ValueType : Position -> Regular
//         T |- ValueType(IteratorType(T))
//  /\ SizeType : Position -> Integer
//         T |- SizeType(IteratorType(T))
//  /\ base : T -> BaseType(T)
//  /\ current : T -> IteratorType(T)
//  /\ begin : T -> IteratorType(T)
//         x |- begin(base(x))
//  /\ end : T -> IteratorType(T)
//         x |- end(base(x))


// concept DynamicSequence(T) means
//     Sequence(T)
//  /\ T supports insert and erase


// concept InsertPosition(T) means
//     Position(T)
//  /\ BaseType : Position -> DynamicSequence

// model InsertPosition(before) /\ InsertPosition(after) /\
//       InsertPosition(front) /\ InsertPosition(back)


// concept ErasePosition(T) means
//     Position(T)
//  /\ BaseType : Position -> DynamicSequence

// model ErasePosition(before) /\ ErasePosition(after) /\
//       ErasePosition(front) /\ ErasePosition(back) /\
//       ErasePosition(at)

template<typename S>
    requires(DynamicSequence(S))
struct before
{
    typedef IteratorType(S) I;
    pointer(S) s;
    I i;
    before(S& s, I i) : s(&s), i(i) { }
};

template<typename S>
    requires(DynamicSequence(S))
struct base_type< before<S> >
{
    typedef S type;
};

template<typename S>
    requires(DynamicSequence(S))
struct iterator_type< before<S> >
{
    typedef IteratorType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct value_type< before<S> >
{
    typedef ValueType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct size_type< before<S> >
{
    typedef DistanceType(IteratorType(S)) type;
};

template<typename S>
    requires(DynamicSequence(S))
S& base(before<S>& p)
{
    return deref(p.s);
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) current(before<S>& p)
{
    return p.i;
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) begin(before<S>& p)
{
    return begin(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) end(before<S>& p)
{
    return end(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
struct after
{
    typedef IteratorType(S) I;
    pointer(S) s;
    I i;
    after(S& s, I i) : s(&s), i(i) { }
};

template<typename S>
    requires(DynamicSequence(S))
struct base_type< after<S> >
{
    typedef S type;
};

template<typename S>
    requires(DynamicSequence(S))
struct iterator_type< after<S> >
{
    typedef IteratorType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct value_type< after<S> >
{
    typedef ValueType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct size_type< after<S> >
{
    typedef DistanceType(IteratorType(S)) type;
};

template<typename S>
    requires(DynamicSequence(S))
S& base(after<S>& p)
{
    return deref(p.s);
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) current(after<S>& p)
{
    return p.i;
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) begin(after<S>& p)
{
    return begin(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) end(after<S>& p)
{
    return end(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
struct front
{
    pointer(S) s;
    front(S& s) : s(&s) { }
};

template<typename S>
    requires(DynamicSequence(S))
struct base_type< front<S> >
{
    typedef S type;
};

template<typename S>
    requires(DynamicSequence(S))
struct iterator_type< front<S> >
{
    typedef IteratorType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct value_type< front<S> >
{
    typedef ValueType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct size_type< front<S> >
{
    typedef DistanceType(IteratorType(S)) type;
};

template<typename S>
    requires(DynamicSequence(S))
S& base(front<S>& p)
{
    return deref(p.s);
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) current(front<S>& p)
{
    return begin(p);
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) begin(front<S>& p)
{
    return begin(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) end(front<S>& p)
{
    return end(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
struct back
{
    pointer(S) s;
    back(S& s) : s(&s) { }
};

template<typename S>
    requires(DynamicSequence(S))
struct base_type< back<S> >
{
    typedef S type;
};

template<typename S>
    requires(DynamicSequence(S))
struct iterator_type< back<S> >
{
    typedef IteratorType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct value_type< back<S> >
{
    typedef ValueType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct size_type< back<S> >
{
    typedef DistanceType(IteratorType(S)) type;
};

template<typename S>
    requires(DynamicSequence(S))
S& base(back<S>& p)
{
    return deref(p.s);
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) current(back<S>& p)
{
    return end(p);
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) begin(back<S>& p)
{
    return begin(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) end(back<S>& p)
{
    return end(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
struct at
{
    typedef IteratorType(S) I;
    pointer(S) s;
    I i;
    at(S& s, I i) : s(&s), i(i) { }
};

template<typename S>
    requires(DynamicSequence(S))
struct base_type< at<S> >
{
    typedef S type;
};

template<typename S>
    requires(DynamicSequence(S))
struct iterator_type< at<S> >
{
    typedef IteratorType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct value_type< at<S> >
{
    typedef ValueType(S) type;
};

template<typename S>
    requires(DynamicSequence(S))
struct size_type< at<S> >
{
    typedef DistanceType(IteratorType(S)) type;
};

template<typename S>
    requires(DynamicSequence(S))
S& base(at<S>& p)
{
    return deref(p.s);
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) current(at<S>& p)
{
    return p.i;
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) begin(at<S>& p)
{
    return begin(base(p));
}

template<typename S>
    requires(DynamicSequence(S))
IteratorType(S) end(at<S>& p)
{
    return end(base(p));
}


// type insert_iterator
// model Iterator(insert_iterator)

template<typename P>
    requires(InsertPosition(P))
struct insert_iterator
{
    typedef insert_iterator I;
    P p;
    insert_iterator(const P& p) : p(p) { }
    void operator=(const ValueType(P)& x) { p = insert(p, x); }
};

template<typename P>
    requires(InsertPosition(P))
struct iterator_type< insert_iterator<P> >
{
    typedef IteratorType(P) type;
};

template<typename P>
    requires(InsertPosition(P))
struct value_type< insert_iterator<P> >
{
    typedef ValueType(P) type;
};

template<typename P>
    requires(InsertPosition(P))
insert_iterator<P>& sink(insert_iterator<P>& i)
{
    return i;
}

template<typename P>
    requires(InsertPosition(P))
insert_iterator<P> successor(const insert_iterator<P>& x)
{
    return x;
}

template<typename P, typename W>
    requires(InsertPosition(P) && Linearizable(W))
P insert_range(P p, const W& w)
{
    return copy(begin(w), end(w), insert_iterator<P>(p)).p;
}

template<typename P, typename I>
    requires(InsertPosition(P) && Readable(I) && Iterator(I))
pair<P, I> insert_range(P p, counted_range<I> w)
{
    pair< I, insert_iterator<P> > io =
        copy_n(begin(w), size(w), insert_iterator<P>(p));
    return pair<P, I>(io.m1.p, io.m0);
}

template<typename S, typename W>
    requires(DynamicSequence(S) && Linearizable(W))
void dynamic_sequence_construction(S& s, const W& w)
{
    construct(s);
    S tmp;
    insert_range(after<S>(tmp, end(tmp)), w);
    swap(s, tmp);
}


// type slist
// model DynamicSequence(slist)

template<typename T>
    requires(Regular(T))
struct slist_node
{
    T value;
    pointer(slist_node) forward_link;
    slist_node(const T& v, pointer(slist_node) f) : value(v), forward_link(f) { }
};

static int slist_node_count = 0; /* ***** TESTING ***** */

template<typename T>
    requires(Regular(T))
struct slist_iterator
{
    pointer(slist_node<T>) p;
    slist_iterator() : p(0) { }
    slist_iterator(pointer(slist_node<T>) p) : p(p) { }
};

template<typename T>
    requires(Regular(T))
struct value_type< slist_iterator<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct distance_type< slist_iterator<T> >
{
    typedef DistanceType(slist_node<T>*) type;
};

template<typename T>
    requires(Regular(T))
struct iterator_concept< slist_iterator<T> >
{
    typedef forward_iterator_tag concept;
};

template<typename T>
    requires(Regular(T))
slist_iterator<T> successor(const slist_iterator<T>& i)
{
    return slist_iterator<T>(source(i.p).forward_link);
}

template<typename I>
    requires(LinkedForwardIterator<I>)
void set_link_forward(I i, I j)
{
    forward_linker<I>()(i, j);
}

template<typename T>
    requires(Regular(T))
bool operator==(slist_iterator<T> i, slist_iterator<T> j)
{
    return i.p == j.p;
}

template<typename T>
    requires(Regular(T))
struct less< slist_iterator<T> >
{
    bool operator()(slist_iterator<T> i,
                    slist_iterator<T> j)
    {
        return i.p < j.p;
    }
};

template<typename T>
    requires(Regular(T))
const T& source(slist_iterator<T> i)
{
    return source(i.p).value;
}

template<typename T>
    requires(Regular(T))
T& sink(slist_iterator<T> i)
{
    return sink(i.p).value;
}

template<typename T>
    requires(Regular(T))
T& deref(slist_iterator<T> i)
{
    return sink(i.p).value;
}

template<typename T>
    requires(Regular(T))
slist_iterator<T> erase_first(slist_iterator<T> i)
{
    slist_iterator<T> j = successor(i);
    destroy(sink(i));
    free(i.p);
    slist_node_count = predecessor(slist_node_count);
    return j;
}

template<typename T,  typename U>
    requires(Regular(T) && Destroyable(T, U))
slist_iterator<T> erase_first(slist_iterator<T> i, U& u)
{
    slist_iterator<T> j = successor(i);
    destroy(sink(i), u);
    free(i.p);
    slist_node_count = predecessor(slist_node_count);
    return j;
}

template<typename T>
    requires(Regular(T))
void erase_after(slist_iterator<T> i)
{
    set_successor(i, erase_first(successor(i)));
}

template<typename T,  typename U>
    requires(Regular(T) && Destroyable(T, U))
void erase_after(slist_iterator<T> i, U& u)
{
    set_successor(i, erase_first(successor(i), u));
}

template<typename T>
    requires(Regular(T))
struct slist
{
    slist_iterator<T> first;
    slist() : first(0) { }
    slist(const slist& x)
    {
        dynamic_sequence_construction(sink(this), x);
    }
    template<typename W>
        requires(Linearizable(W) && T == ValueType(W))
    slist(const W& w)
    {
        dynamic_sequence_construction(sink(this), w);
    }
    void operator=(slist x)
    {
        swap(deref(this), x);
    }
    T& operator[](DistanceType(slist_iterator<T>) i)
    {
        return deref(first + i);
    }
    ~slist()
    {
        erase_all(sink(this));
    }
};

template<typename T>
    requires(Regular(T))
struct iterator_type< slist<T> >
{
    typedef slist_iterator<T> type;
};

template<typename T>
    requires(Regular(T))
struct value_type< slist<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct size_type< slist<T> >
{
    typedef DistanceType(IteratorType(slist<T>)) type;
};

template<typename T>
    requires(Regular(T))
struct underlying_type< slist<T> >
{
    typedef slist_iterator<T> type; // or IteratorType(slist<T>)
};

template<typename T>
    requires(Regular(T))
IteratorType(slist<T>) begin(const slist<T>& x)
{
    return x.first;
}

template<typename T>
    requires(Regular(T))
IteratorType(slist<T>) end(const slist<T>&)
{
    return slist_iterator<T>();
}

// size, empty subsumed by definitions for Linearizeable

template<typename T>
    requires(Regular(T))
void erase_all(slist<T>& x)
{
    while (!empty(x)) x.first = erase_first(begin(x));
}

template<typename T>
    requires(Regular(T))
bool operator==(const slist<T>& x, const slist<T>& y)
{
    return linearizable_equal(x, y);
}

template<typename T>
    requires(Regular(T))
bool operator<(const slist<T>& x, const slist<T>& y)
{
    return linearizable_ordering(x, y);
}

template<typename T,  typename U>
    requires(Regular(T) && Constructible(T, U))
after< slist<T> > insert(after< slist<T> > p, const U& u)
{
    slist_node_count = successor(slist_node_count);
    slist_iterator<T> i((slist_node<T>*)malloc(sizeof(slist_node<T>)));
    construct(sink(i), u);
    if (current(p) == end(p)) {
        set_link_forward(i, begin(p));
        base(p).first = i;
    } else {
        set_link_forward(i, successor(current(p)));
        set_link_forward(current(p), i);
    }
    return after< slist<T> >(base(p), i);
}

template<typename T>
    requires(Regular(T))
void reverse(slist<T>& x)
{
    typedef IteratorType(slist<T>) I;
    x.first = reverse_append(begin(x), end(x), end(x), forward_linker<I>());
}

template<typename T, typename P>
    requires(Regular(T) && UnaryPredicate(P) && Domain(P) == T)
void partition(slist<T>& x, slist<T>& y, P p)
{
    typedef IteratorType(slist<T>) I;
    pair< pair<I, I>, pair<I, I> > pp =
        partition_linked(begin(x), end(x), p, forward_linker<I>());
    x.first = pp.m0.m0;
    if (pp.m0.m0 != end(x))
        forward_linker<I>()(pp.m0.m1, end(x));
    if (pp.m1.m0 != end(x)) {
        forward_linker<I>()(pp.m1.m1, begin(y));
        y.first = pp.m1.m0;
    }
}

template<typename T, typename R>
    requires(Regular(T) && Regular(R) && Domain(R) == T)
void merge(slist<T>& x, slist<T>& y, R r)
{
    // Precondition: $\func{weak\_ordering}(r)$
    typedef IteratorType(slist<T>) I;
    if (empty(y)) return;
    if (empty(x)) { swap(x, y); return; }
    x.first = merge_linked_nonempty(
                  begin(x), end(x), begin(y), end(y),
                  r, forward_linker<I>()).m0;
    y.first = end(y); // former nodes of y now belong to x
}

template<typename T, typename R>
    requires(Regular(T) && Relation(R) && Domain(R) == T)
void sort(slist<T>& x, R r)
{
    // Precondition: $\func{weak\_ordering}(r)$
    typedef IteratorType(slist<T>) I;
    pair<I, I> p = sort_linked_nonempty_n(begin(x), size(x), r, forward_linker<I>());
    x.first = p.m0;
}


// type list
// model DynamicSequence(list)

template<typename T>
    requires(Regular(T))
struct list_node
{
    T value;
    pointer(list_node) forward_link;
    pointer(list_node) backward_link;
    list_node(
        const T& v,
        pointer(list_node) f, pointer(list_node) b) :
        value(v), forward_link(f), backward_link(b) { }
};

static int list_node_count = 0; /* ***** TESTING ***** */

template<typename T>
    requires(Regular(T))
struct list_iterator
{
    pointer(list_node<T>) p;
    list_iterator() : p(0) { }
    list_iterator(pointer(list_node<T>) p) : p(p) { }
};

template<typename T>
    requires(Regular(T))
struct value_type< list_iterator<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct distance_type< list_iterator<T> >
{
    typedef DistanceType(list_node<T>*) type;
};

template<typename T>
    requires(Regular(T))
struct iterator_concept< list_iterator<T> >
{
    typedef bidirectional_iterator_tag concept;
};

template<typename T>
    requires(Regular(T))
list_iterator<T> successor(const list_iterator<T>& i)
{
    return list_iterator<T>(source(i.p).forward_link);
}

template<typename T>
    requires(Regular(T))
list_iterator<T> predecessor(const list_iterator<T>& i)
{
    return list_iterator<T>(source(i.p).backward_link);
}

template<typename I>
    requires(LinkedBidirectionalIterator<I>)
void set_link_backward(I i, I j)
{
    backward_linker<I>()(i, j);
}

template<typename I>
    requires(LinkedForwardIterator<I>)
void set_link_bidirectional(I i, I j)
{
    bidirectional_linker<I>()(i, j);
}

template<typename T>
    requires(Regular(T))
bool operator==(list_iterator<T> i, list_iterator<T> j)
{
    return i.p == j.p;
}

template<typename T>
    requires(Regular(T))
struct less< list_iterator<T> >
{
    bool operator()(list_iterator<T> i,
                    list_iterator<T> j)
    {
        return i.p < j.p;
    }
};

template<typename T>
    requires(Regular(T))
const T& source(list_iterator<T> i)
{
    return source(i.p).value;
}

template<typename T>
    requires(Regular(T))
T& sink(list_iterator<T> i)
{
    return sink(i.p).value;
}

template<typename T>
    requires(Regular(T))
T& deref(list_iterator<T> i)
{
    return sink(i.p).value;
}

template<typename T>
    requires(Regular(T))
void erase(list_iterator<T> i)
{
    set_link_bidirectional(predecessor(i), successor(i));
    destroy(sink(i));
    free(i.p);
    list_node_count = predecessor(list_node_count);
}

template<typename T,  typename U>
    requires(Regular(T) && Destroyable(T, U))
void erase(list_iterator<T> i, U& u)
{
    set_link_bidirectional(predecessor(i), successor(i));
    destroy(sink(i), u);
    free(i.p);
    list_node_count = predecessor(list_node_count);
}

template<typename T>
    requires(Regular(T))
struct list
{
    list_iterator<T> dummy;
    list() : dummy((list_node<T>*)malloc(sizeof(list_node<T>)))
    {
        // The dummy node's value is never constructed
        set_link_bidirectional(dummy, dummy);
    }
    list(const list& x)
    {
        dynamic_sequence_construction(sink(this), x);
    }
    template<typename W>
        requires(Linearizable(W))
    list(const W& w)
    {
        dynamic_sequence_construction(sink(this), w);
    }
    void operator=(list x)
    {
        swap(deref(this), x);
    }
    T& operator[](DistanceType(list_iterator<T>) i)
    {
        return deref(begin(deref(this)) + i);
    }
    ~list()
    {
        erase_all(sink(this));
        // We do not destroy the dummy node's value since it was not constructed
        free(dummy.p);
    }
};

template<typename T>
    requires(Regular(T))
struct iterator_type< list<T> >
{
    typedef list_iterator<T> type;
};

template<typename T>
    requires(Regular(T))
struct value_type< list<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct size_type< list<T> >
{
    typedef DistanceType(IteratorType(list<T>)) type;
};

template<typename T>
    requires(Regular(T))
struct underlying_type< list<T> >
{
    typedef list_iterator<T> type; // or IteratorType(list<T>)
};

template<typename T>
    requires(Regular(T))
IteratorType(list<T>) begin(const list<T>& x)
{
    return successor(x.dummy);
}

template<typename T>
    requires(Regular(T))
IteratorType(list<T>) end(const list<T>& x)
{
    return x.dummy;
}

// size, empty subsumed by definitions for Linearizeable

template<typename T>
    requires(Regular(T))
void erase_all(list<T>& x)
{
    while (!empty(x)) erase(predecessor(end(x)));
}

template<typename T>
    requires(Regular(T))
bool operator==(const list<T>& x, const list<T>& y)
{
    return linearizable_equal(x, y);
}

template<typename T>
    requires(Regular(T))
bool operator<(const list<T>& x, const list<T>& y)
{
    return linearizable_ordering(x, y);
}

template<typename T,  typename U>
    requires(Regular(T) && Constructible(T, U))
list_iterator<T> insert(list_iterator<T> j, const U& u)
{
    list_node_count = successor(list_node_count);
    list_iterator<T> i((list_node<T>*)malloc(sizeof(list_node<T>)));
    construct(sink(i), u);
    set_link_bidirectional(predecessor(j), i);
    set_link_bidirectional(i, j);
    return i;
}

template<typename T,  typename U>
    requires(Regular(T) && Constructible(T, U))
after< list<T> > insert(after< list<T> > p, const U& u)
{
    return after< list<T> >(base(p), insert(successor(current(p)), u));
}

template<typename T>
    requires(Regular(T))
void reverse(list<T>& x)
{
    typedef IteratorType(list<T>) I;
    I i = reverse_append(begin(x), end(x), end(x), bidirectional_linker<I>());
    set_link_bidirectional(x.dummy, i);
}

template<typename T, typename P>
    requires(Regular(T) && UnaryPredicate(P) && Domain(P) == T)
void partition(list<T>& x, list<T>& y, P p)
{
    typedef IteratorType(list<T>) I;
    bidirectional_linker<I> set_link;
    pair< pair<I, I>, pair<I, I> > pp =
        partition_linked(begin(x), end(x), p, set_link);
    set_link(pp.m0.m1, x.dummy);
    set_link(x.dummy, pp.m0.m0);
    if (pp.m1.m0 != end(x)) {
        set_link(pp.m1.m1, begin(y));
        set_link(y.dummy, pp.m1.m0);
    }
}

template<typename T, typename R>
    requires(Regular(T) && Regular(R) && Domain(R) == T)
void merge(list<T>& x, list<T>& y, R r)
{
    // Precondition: $\func{weak\_ordering}(r)$
    typedef IteratorType(list<T>) I;
    bidirectional_linker<I> set_link;
    if (empty(y)) return;
    if (empty(x)) { swap(x, y); return; }
    pair<I, I> p = merge_linked_nonempty(
                  begin(x), end(x), begin(y), end(y),
                  r, set_link);
    set_link(x.dummy, p.m0);
    set_link(find_last(p.m0, p.m1), x.dummy);
    set_link(y.dummy, y.dummy); // former nodes of y now belong to x
}

template<typename T, typename R>
    requires(Regular(T) && Relation(R) && Domain(R) == T)
void sort(list<T>& x, R r)
{
    // Precondition: $\func{weak\_ordering}(r)$
    typedef IteratorType(list<T>) I;
    pair<I, I> p = sort_linked_nonempty_n(begin(x), size(x), r, forward_linker<I>());
    // See the end of section 8.3 of Elements of Programming
    // for the explanation of this relinking code:
    bidirectional_linker<I>()(x.dummy, p.m0);
    I f = p.m0;
    while (f != p.m1) {
        backward_linker<I>()(f, successor(f));
        f = successor(f);
    }
}


// concept BinaryTree means ...


// type stree
// model BinaryTree(stree)

template<typename T>
    requires(Regular(T))
struct stree_node
{
    typedef pointer(stree_node) Link;
    T value;
    Link left_successor_link;
    Link right_successor_link;
    stree_node() : left_successor_link(0), right_successor_link(0) { }
    stree_node(T v, Link l = 0, Link r = 0) :
        value(v),
        left_successor_link(l), right_successor_link(r) { }
};

template<typename T>
    requires(Regular(T))
struct stree_coordinate
{
    pointer(stree_node<T>) ptr;
    stree_coordinate() : ptr(0) { }
    stree_coordinate(pointer(stree_node<T>) ptr) : ptr(ptr) { }
};

template<typename T>
    requires(Regular(T))
struct value_type< stree_coordinate<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct weight_type< stree_coordinate<T> >
{
    typedef DistanceType(pointer(stree_node<T>)) type;
};

template<typename T>
    requires(Regular(T))
bool empty(stree_coordinate<T> c)
{
    typedef pointer(stree_node<T>) I;
    return c.ptr == I(0);
}

template<typename T>
    requires(Regular(T))
stree_coordinate<T> left_successor(stree_coordinate<T> c)
{
    return source(c.ptr).left_successor_link;
}

template<typename T>
    requires(Regular(T))
stree_coordinate<T> right_successor(stree_coordinate<T> c)
{
    return source(c.ptr).right_successor_link;
}

template<typename T>
    requires(Regular(T))
bool has_left_successor(stree_coordinate<T> c)
{
    return !empty(left_successor(c));
}

template<typename T>
    requires(Regular(T))
bool has_right_successor(stree_coordinate<T> c)
{
    return !empty(right_successor(c));
}

template<typename T>
    requires(Regular(T))
void set_left_successor(stree_coordinate<T> c, stree_coordinate<T> l)
{
    sink(c.ptr).left_successor_link = l.ptr;
}

template<typename T>
    requires(Regular(T))
void set_right_successor(stree_coordinate<T> c, stree_coordinate<T> r)
{
    sink(c.ptr).right_successor_link = r.ptr;
}

template<typename T>
    requires(Regular(T))
bool operator==(stree_coordinate<T> c0, stree_coordinate<T> c1)
{
    return c0.ptr == c1.ptr;
}

template<typename T>
    requires(Regular(T))
const T& source(stree_coordinate<T> c)
{
    return source(c.ptr).value;
}

template<typename T>
    requires(Regular(T))
T& sink(stree_coordinate<T> c)
{
    return sink(c.ptr).value;
}

static int stree_node_count = 0; /* ***** TESTING ***** */

template<typename T>
    requires(Regular(T))
struct stree_node_construct
{
    typedef stree_coordinate<T> C;
    stree_node_construct() { }
    C operator()(T x, C l = C(0), C r = C(0))
    {
        ++stree_node_count;
        return C(new stree_node<T>(x, l.ptr, r.ptr));
    }
    C operator()(C c)           { return (*this)(source(c), left_successor(c),
                                                            right_successor(c)); }
    C operator()(C c, C l, C r) { return (*this)(source(c), l, r); }
};

template<typename T>
    requires(Regular(T))
struct stree_node_destroy
{
    stree_node_destroy() { }
    void operator()(stree_coordinate<T> i)
    {
        --stree_node_count;
        delete i.ptr;
    }
};

template<typename C, typename ND>
    requires(BifurcateCoordinate(C) && TreeNodeDeleter(ND))
void bifurcate_erase(C c, ND node_delete)
{
    if (empty(c)) return;
    C stack = C(0); // chained through left_successor
    while (true) {
        C left = left_successor(c);
        C right = right_successor(c);
        if (!empty(left)) {
            if (!empty(right)) {
                set_left_successor(c, stack);
                stack = c;
            } else
                node_delete(c);
            c = left;
        } else if (!empty(right)) {
            node_delete(c);
            c = right;
        } else {
            node_delete(c);
            if (!empty(stack)) {
                c = stack;
                stack = left_successor(stack);
                set_left_successor(c, C(0));
           } else return;
        }
    }
}

/*
   The next function is based on MAKECOPY in this paper:

   K. P. Lee.
   A linear algorithm for copying binary trees using bounded workspace.
   Commun. ACM 23, 3 (March 1980), 159-162. DOI=10.1145/358826.358835
   http://doi.acm.org/10.1145/358826.358835
*/

template<typename C, typename Cons>
    requires(EmptyLinkedBifurcateCoordinate(C) &&
        TreeNodeConstructor(Cons) && NodeType(C) == NodeType(Cons))
C bifurcate_copy(C c)
{
    Cons construct_node;
    if (empty(c)) return c;              // Us      / Lee
    C stack = construct_node(c, c, C()); // stack   / V'
    C c_new = stack;                     // c\_new  / COPY
    while (!empty(stack)) {              // empty() / null
        c = left_successor(stack);       // c       / V
        C l = left_successor(c);
        C r = right_successor(c);
        C top = stack;
        if (!empty(l)) {
            if (!empty(r)) {
                r = construct_node(r, r, right_successor(stack));
                stack = construct_node(l, l, r);
            }
            else  {
                r = C();
                stack = construct_node(l, l, right_successor(stack));
            }
            l = stack;
        } else if (!empty(r)) {
            stack = construct_node(r, r, right_successor(stack));
            r = stack;
        } else
            stack = right_successor(stack);
        set_right_successor(top, r);
        set_left_successor(top, l);
    }
    return c_new;
}

template<typename T>
    requires(Regular(T))
struct stree
{
    typedef stree_coordinate<T> C;
    typedef stree_node_construct<T> Cons;
    C root;
    stree() : root(0) { }
    stree(T x) : root(Cons()(x)) { }
    stree(T x, const stree& left, const stree& right) : root(Cons()(x))
    {
        set_left_successor(root, bifurcate_copy<C, Cons>(left.root));
        set_right_successor(root, bifurcate_copy<C, Cons>(right.root));
    }
    stree(const stree& x) : root(bifurcate_copy<C, Cons>(x.root)) { }
    ~stree() { bifurcate_erase(root, stree_node_destroy<T>()); }
    void operator=(stree x) { swap(root, x.root); }
};

template<typename T>
    requires(Regular(T))
struct coordinate_type< stree<T> >
{
    typedef stree_coordinate<T> type;
};

template<typename T>
    requires(Regular(T))
struct value_type< stree<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct weight_type< stree<T> >
{
    typedef WeightType(CoordinateType(stree<T>)) type;
};

template<typename T>
    requires(Regular(T))
stree_coordinate<T> begin(const stree<T>& x) { return x.root; }

template<typename T>
    requires(Regular(T))
bool empty(const stree<T>& x) { return empty(x.root); }

template<typename T>
    requires(Regular(T))
bool operator==(const stree<T>& x, const stree<T>& y)
{
    if (empty(x)) return empty(y);
    if (empty(y)) return false;
    return bifurcate_equivalent_nonempty(begin(x), begin(y), equal<T>());
}

template<typename T>
    requires(Regular(T))
bool operator<(const stree<T>& x, const stree<T>& y)
{
    if (empty(x)) return !empty(y);
    if (empty(y)) return false;
    less<T> lt;
    return 1 == bifurcate_compare_nonempty(
        begin(x), begin(y),
        comparator_3_way< less<T> >(lt));
}

template<typename T, typename Proc>
    requires(Regular(T) &&
        Procedure(Proc) && Arity(Proc) == 2 &&
        visit == InputType(Proc, 0) &&
        CoordinateType(stree<T>) == InputType(Proc, 1))
void traverse(stree<T>& x, Proc proc)
{
    traverse_nonempty(begin(x), proc);
}


// type tree
// model BinaryTree(tree)

template<typename T>
    requires(Regular(T))
struct tree_node
{
    typedef pointer(tree_node) Link;
    T value;
    Link left_successor_link;
    Link right_successor_link;
    Link predecessor_link;
    tree_node() :
        left_successor_link(0), right_successor_link(0),
        predecessor_link(0) { }
    tree_node(T v, Link l = 0, Link r = 0, Link p = 0) :
        value(v),
        left_successor_link(l), right_successor_link(r),
        predecessor_link(p) { }
};

template<typename T>
    requires(Regular(T))
struct tree_coordinate
{
    pointer(tree_node<T>) ptr;
    tree_coordinate() : ptr(0) { }
    tree_coordinate(pointer(tree_node<T>) ptr) : ptr(ptr) { }
};

template<typename T>
    requires(Regular(T))
struct value_type< tree_coordinate<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct weight_type< tree_coordinate<T> >
{
    typedef DistanceType(pointer(tree_node<T>)) type;
};

template<typename T>
    requires(Regular(T))
bool empty(tree_coordinate<T> c)
{
    return c.ptr == 0;
}

template<typename T>
    requires(Regular(T))
tree_coordinate<T> left_successor(tree_coordinate<T> c)
{
    return source(c.ptr).left_successor_link;
}

template<typename T>
    requires(Regular(T))
tree_coordinate<T> right_successor(tree_coordinate<T> c)
{
    return source(c.ptr).right_successor_link;
}

template<typename T>
    requires(Regular(T))
bool has_left_successor(tree_coordinate<T> c)
{
    return !empty(left_successor(c));
}

template<typename T>
    requires(Regular(T))
bool has_right_successor(tree_coordinate<T> c)
{
    return !empty(right_successor(c));
}

template<typename T>
    requires(Regular(T))
tree_coordinate<T> predecessor(tree_coordinate<T> c)
{
    return source(c.ptr).predecessor_link;
}

template<typename T>
    requires(Regular(T))
bool has_predecessor(tree_coordinate<T> c)
{
    return !empty(predecessor(c));
}

template<typename T>
    requires(Regular(T))
void set_predecessor(tree_coordinate<T> c, tree_coordinate<T> p)
{
    sink(c.ptr).predecessor_link = p.ptr;
}

template<typename T>
    requires(Regular(T))
void set_left_successor(tree_coordinate<T> c, tree_coordinate<T> l)
{
    sink(c.ptr).left_successor_link = l.ptr;
    if (!empty(l)) set_predecessor(l, c);
}

template<typename T>
    requires(Regular(T))
void set_right_successor(tree_coordinate<T> c, tree_coordinate<T> r)
{
    sink(c.ptr).right_successor_link = r.ptr;
    if (!empty(r)) set_predecessor(r, c);
}

template<typename T>
    requires(Regular(T))
bool operator==(tree_coordinate<T> c0, tree_coordinate<T> c1)
{
    return c0.ptr == c1.ptr;
}

template<typename T>
    requires(Regular(T))
const T& source(tree_coordinate<T> c)
{
    return source(c.ptr).value;
}

template<typename T>
    requires(Regular(T))
T& sink(tree_coordinate<T> c)
{
    return sink(c.ptr).value;
}

static int tree_node_count = 0; /* ***** TESTING ***** */

template<typename T>
    requires(Regular(T))
struct tree_node_construct
{
    typedef tree_coordinate<T> C;
    tree_node_construct() { }
    C operator()(T x, C l = C(0), C r = C(0))
    {
        ++tree_node_count;
        return C(new tree_node<T>(x, l.ptr, r.ptr));
    }
    C operator()(C c)           { return (*this)(source(c), left_successor(c),
                                                            right_successor(c)); }
    C operator()(C c, C l, C r) { return (*this)(source(c), l, r); }
};

template<typename T>
    requires(Regular(T))
struct tree_node_destroy
{
    tree_node_destroy() { }
    void operator()(tree_coordinate<T> i)
    {
        --tree_node_count;
        delete i.ptr;
    }
};

template<typename T>
    requires(Regular(T))
struct tree
{
    typedef tree_coordinate<T> C;
    typedef tree_node_construct<T> Cons;
    C root;
    tree() : root(0) { }
    tree(T x) : root(Cons()(x)) { }
    tree(T x, const tree& left, const tree& right) : root(Cons()(x))
    {
        set_left_successor(root, bifurcate_copy<C, Cons>(left.root));
        set_right_successor(root, bifurcate_copy<C, Cons>(right.root));
    }
    tree(const tree& x) : root(bifurcate_copy<C, Cons>(x.root)) { }
    ~tree()
    {
        bifurcate_erase(root, tree_node_destroy<T>());
    }
    void operator=(tree x)
    {
        swap(root, x.root);
    }
};

template<typename T>
    requires(Regular(T))
struct coordinate_type< tree<T> >
{
    typedef tree_coordinate<T> type;
};

template<typename T>
    requires(Regular(T))
struct value_type< tree<T> >
{
    typedef ValueType(CoordinateType(tree<T>)) type;
};

template<typename T>
    requires(Regular(T))
struct weight_type< tree<T> >
{
    typedef WeightType(CoordinateType(tree<T>)) type;
};

template<typename T>
    requires(Regular(T))
tree_coordinate<T> begin(const tree<T>& x)
{
    return x.root;
}

template<typename T>
    requires(Regular(T))
bool empty(const tree<T>& x)
{
    return empty(x.root);
}

template<typename T>
    requires(Regular(T))
bool operator==(const tree<T>& x, const tree<T>& y)
{
    return bifurcate_equal(begin(x), begin(y));
}

template<typename T>
    requires(Regular(T))
bool operator<(const tree<T>& x, const tree<T>& y)
{
    return bifurcate_less(begin(x), begin(y));
}

template<typename T, typename Proc>
    requires(Regular(T) &&
        Procedure(Proc) && Arity(Proc) == 2 &&
        visit == InputType(Proc, 0) &&
        CoordinateType(tree<T>) == InputType(Proc, 1))
void traverse(tree<T>& x, Proc proc)
{
    traverse(begin(x), proc);
}


// type array
// model DynamicSequence(array)

template<typename T>
    requires(Regular(T))
struct array_prefix
{
    pointer(T) m;
    pointer(T) l;
    T  a;
    // Invariant: $[addressof(a), m)$ are constructed elements
    // Invariant: $[m, l)$ are unconstructed (reserve) elements
};

template<typename T>
    requires(Regular(T))
pointer(array_prefix<T>) allocate_array(DistanceType(T*) n)
{
    typedef pointer(array_prefix<T>) P;
    if (zero(n)) return P(0);
    int bsize = int(predecessor(n)) * sizeof(T);
    P p = P(malloc(sizeof(array_prefix<T>) + bsize));
    pointer(T) f = &sink(p).a;
    sink(p).m = f;
    sink(p).l = f + n;
    return p;
}

template<typename T>
    requires(Regular(T))
void deallocate_array(pointer(array_prefix<T>) p)
{
    free(p);
}

template<typename T>
    requires(Regular(T))
struct array
{
    typedef DistanceType(IteratorType(array<T>)) N;
    pointer(array_prefix<T>) p;
    array() : p(0) { }
    array(N c) : p(allocate_array<T>(c)) { } // size is 0 and capacity is c
    array(N s, N c, const T& x)
        : p(allocate_array<T>(c)) // size is s, capacity is c, all elements equal to x
    {
        while (!zero(s)) { push(sink(this), x); s = predecessor(s); }
    }
    array(const array& x) : p(allocate_array<T>(size(x)))
    {
        insert_range(back< array<T> >(sink(this)), x);
    }
    template<typename W>
        requires(Linearizable(W) && T == ValueType(W))
    array(const W& w) : p(allocate_array<T>(0))
    {
        insert_range(back< array<T> >(sink(this)), w);
    }
    template<typename I>
        requires(Readable(I) && Iterator(I) && T == ValueType(I))
    array(const counted_range<I>& w) : p(allocate_array<T>(size(w)))
    {
        insert_range(back< array<T> >(sink(this)), w);
    }
    void operator=(array x)
    {
        swap(deref(this), x);
    }
    T& operator[](N i)
    {
        return deref(begin(deref(this)) + i);
    }
    const T& operator[](N i) const
    {
        return deref(begin(deref(this)) + i);
    }
    ~array()
    {
        erase_all(sink(this));
    }
};

template<typename T>
    requires(Regular(T))
struct iterator_type< array<T> >
{
    typedef pointer(T) type;
};

template<typename T>
    requires(Regular(T))
struct value_type< array<T> >
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct size_type< array<T> >
{
    typedef DistanceType(IteratorType(array<T>)) type;
};

template<typename T>
    requires(Regular(T))
struct underlying_type< array<T> >
{
    typedef struct { pointer(array_prefix<T>) p; } type;
};

template<typename T>
    requires(Regular(T))
IteratorType(array<T>) begin(const array<T>& x)
{
    typedef pointer(array_prefix<T>) P;
    typedef IteratorType(array<T>) I;
    if (x.p == P(0)) return I(0);
    return I(addressof(source(x.p).a));
}

template<typename T>
    requires(Regular(T))
IteratorType(array<T>) end(const array<T>& x)
{
    typedef pointer(array_prefix<T>) P;
    typedef IteratorType(array<T>) I;
    if (x.p == P(0)) return I(0);
    return I(source(x.p).m);
}

template<typename T>
    requires(Regular(T))
IteratorType(array<T>) end_of_storage(const array<T>& x)
{
    typedef pointer(array_prefix<T>) P;
    typedef IteratorType(array<T>) I;
    if (x.p == P(0)) return I(0);
    return I(source(x.p).l);
}

template<typename T>
    requires(Regular(T))
DistanceType(IteratorType(array<T>)) capacity(const array<T>& x)
{
    return end_of_storage(x) - begin(x);
}

template<typename T>
    requires(Regular(T))
bool full(const array<T>& x)
{
    return end(x) == end_of_storage(x);
}

template<typename T>
    requires(Regular(T))
bool operator==(const array<T>& x, const array<T>& y)
{
    return linearizable_equal(x, y);
}

template<typename T>
    requires(Regular(T))
bool operator<(const array<T>& x, const array<T>& y)
{
    return linearizable_ordering(x, y);
}

template<typename T, typename U>
    requires(Regular(T) && Regular(U) && Constructible(T, U))
back< array<T> > insert(back< array<T> > p, const U& y)
{
    typedef DistanceType(IteratorType(array<T>)) N;
    N n = size(base(p));
    if (n == capacity(base(p)))
        reserve(base(p), max(N(1), n + n));
    construct(sink(source(base(p).p).m), y);
    sink(base(p).p).m = successor(sink(base(p).p).m);
    return p;
}

template<typename T, typename W>
    requires(Regular(T) &&
        Linearizable(W) && Constructible(T, ValueType(W)))
before< array<T> > insert_range(before< array<T> > p, const W& w)
{
    typedef IteratorType(array<T>) I;
    DistanceType(I) o_f = current(p) - begin(p);
    DistanceType(I) o_m = size(p);
    insert_range(back< array<T> >(base(p)), w);
    return before< array<T> >(base(p), rotate(begin(p) + o_f, begin(p) + o_m, end(p)));
}
// Note that for iterators supporting fast subtraction,
// we could write a somewhat faster but also much more complex
// version (complexity mostly dealing with exception safety)

template<typename T>
    requires(Regular(T))
back< array<T> > erase(back< array<T> > x)
{
    --sink(deref(x.s).p).m;
    destroy(sink(source(deref(x.s).p).m));
    if (empty(deref(x.s))) {
        deallocate_array(deref(x.s).p);
        deref(x.s).p = 0;
    }
    return x;
}

template<typename T>
    requires(Regular(T))
void erase_all(array<T>& x)
{
    while (!empty(x)) erase(back< array<T> >(x));
}

template<typename T>
    requires(Regular(T))
void swap_basic(T& x, T& y)
{
    T tmp = x;
    x = y;
    y = tmp;
}

template<typename T>
    requires(Regular(T))
UnderlyingType(T)& underlying_ref(T& x)
{
    return reinterpret_cast<UnderlyingType(T)&>(x);
}

template<typename T>
    requires(Regular(T))
const UnderlyingType(T)& underlying_ref(const T& x)
{
    return reinterpret_cast<UnderlyingType(T)&>(const_cast<T&>(x));
}

template<typename T>
    requires(Regular(T))
void swap(T& x, T& y)
{
    UnderlyingType(T) tmp = underlying_ref(x);
    underlying_ref(x)     = underlying_ref(y);
    underlying_ref(y)     = tmp;
}


// Exercise 12.9:

template<typename I>
  requires(Iterator(I))
struct underlying_iterator
{
    I i;
    underlying_iterator() { }
    underlying_iterator(const I& x) : i(x) { }
};

template<typename I>
    requires(Iterator(I))
struct value_type< underlying_iterator<I> >
{
    typedef UnderlyingType(ValueType(I)) type;
};

template<typename I>
    requires(Iterator(I))
struct distance_type< underlying_iterator<I> >
{
    typedef DistanceType(I) type;
};

template<typename I>
    requires(Iterator(I))
struct iterator_concept< underlying_iterator<I> >
{
    typedef IteratorConcept(I) concept;
};

template<typename I>
    requires(Iterator(I))
underlying_iterator<I> successor(const underlying_iterator<I>& x)
{
  return successor(x.i);
}

template<typename I>
    requires(Iterator(I))
underlying_iterator<I> predecessor(const underlying_iterator<I>& x)
{
  return predecessor(x.i);
}

template<typename I>
    requires(Iterator(I))
underlying_iterator<I> operator+(underlying_iterator<I> x, DistanceType(I) n)
{
    return underlying_iterator<I>(x.i + n);
}

template<typename I>
    requires(Iterator(I))
DistanceType(I) operator-(underlying_iterator<I> x, underlying_iterator<I> y)
{
    return x.i - y.i;
}

template<typename I>
    requires(Iterator(I))
underlying_iterator<I> operator-(underlying_iterator<I> x, DistanceType(I) n)
{
    return underlying_iterator<I>(x.i - n);
}

template<typename I>
    requires(Iterator(I))
bool operator==(const underlying_iterator<I>& x, const underlying_iterator<I>& y)
{
    return x.i == y.i;
}

template<typename I>
    requires(Iterator(I))
bool operator<(const underlying_iterator<I>& x, const underlying_iterator<I>& y)
{
    return x.i < y.i;
}

template<typename I>
    requires(Iterator(I))
const UnderlyingType(ValueType(I))& source(const underlying_iterator<I>& x)
{
  return underlying_ref(source(x.i));
}

template<typename I>
    requires(Iterator(I))
UnderlyingType(ValueType(I))& sink(underlying_iterator<I>& x)
{
  return underlying_ref(sink(x.i));
}

template<typename i>
    requires(Iterator(i))
UnderlyingType(ValueType(i))& deref(underlying_iterator<i>& x)
{
  return underlying_ref(deref(x.i));
}

template<typename I>
    requires(Iterator(I))
I original(const underlying_iterator<I>& x)
{
    return x.i;
}


// Project 12.5: here are some more techniques and examples:

template<typename T>
    requires(Regular(T))
void reserve_basic(array<T>& x,
                   DistanceType(IteratorType(array<T>)) n)
{
    if (n < size(x) || n == capacity(x)) return;
    array<T> tmp(n);
    insert_range(back< array<T> >(tmp), x);
    swap(tmp, x);
}

template<typename T>
    requires(Regular(T))
void reserve(array<T>& x, DistanceType(IteratorType(array<T>)) n)
{
    reserve_basic(reinterpret_cast<array<UnderlyingType(T)>&>(x), n);
}


// In order to adapt algorithms with predicates and relations as
// arguments, we use adapters that cast from the underlying type to the
// original type before calling the predicate or relation:

template<typename T>
    requires(Regular(T))
T& original_ref(UnderlyingType(T)& x)
{
    return reinterpret_cast<T&>(x);
}

template<typename T>
    requires(Regular(T))
const T& original_ref(const UnderlyingType(T)& x)
{
    return reinterpret_cast<const T&>(x);
}

template<typename P>
    requires(Predicate(P))
struct underlying_predicate
{
    typedef UnderlyingType(Domain(P)) U;
    P p;
    underlying_predicate(P p) : p(p) { }
    bool operator()(const U& x)
    {
        return p(original_ref<Domain(P)>(x));
    }
};

template<typename P>
    requires(Predicate(P))
struct input_type< underlying_predicate<P>, 0>
{
    typedef UnderlyingType(Domain(P)) type;
};

template<typename R>
    requires(Relation(R))
struct underlying_relation
{
    typedef UnderlyingType(Domain(R)) U;
    R r;
    underlying_relation(R r) : r(r) { }
    bool operator()(const U& x, const U& y)
    {
        return r(original_ref<Domain(R)>(x), original_ref<Domain(R)>(y));
    }
};

template<typename R>
    requires(Relation(R))
struct input_type< underlying_relation<R>, 0>
{
    typedef UnderlyingType(Domain(R)) type;
};

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, I> advanced_partition_stable_n(I f, DistanceType(I) n, P p)
{
    typedef underlying_iterator<I> U;
    pair<U, U> tmp = partition_stable_n(U(f), n,
                                        underlying_predicate<P>(p));
    return pair<I, I>(original(tmp.m0), original(tmp.m1));
}

template<typename I, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Relation(R) && ValueType(I) == Domain(R))
I advanced_sort_n(I f, DistanceType(I) n, R r)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    temporary_buffer<UnderlyingType(ValueType(I))> b(half_nonnegative(n));
    return original(sort_n_adaptive(underlying_iterator<I>(f), n,
                                    begin(b), size(b),
                                    underlying_relation<R>(r)));
}

template<typename T, typename R>
    requires(Regular(T) && Relation(R) && Domain(R) == T)
void sort(array<T>& x, R r)
{
    // Precondition: $\func{weak\_ordering}(r)$
    advanced_sort_n(begin(x), size(x), r);
}

#endif // EOP_EOP
*/
