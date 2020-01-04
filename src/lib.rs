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
    clippy::type_repetition_in_bounds,
    clippy::use_self
)]
use num::{NumCast, One, Zero};
mod integers;
use integers::{
    binary_scale_up_nonnegative, even, half_nonnegative, odd, one, predecessor, successor, twice,
    zero, Integer, Regular,
};
use std::marker::PhantomData;
#[macro_use]
extern crate typenum;
use typenum::{private::IsLessPrivate, Cmp, Compare, False, IsLess, True, P1, P2, P3, P4, Z0};

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

pub trait BinaryOperation<Domain> {
    fn call(&self, x: &Domain, y: &Domain) -> Domain;
}

impl<Domain, T> BinaryOperation<Domain> for T
where
    T: Fn(&Domain, &Domain) -> Domain,
{
    fn call(&self, x: &Domain, y: &Domain) -> Domain {
        self(x, y)
    }
}

pub fn square_1<Domain, Op>(x: &Domain, op: &Op) -> Domain
where
    Op: BinaryOperation<Domain>,
{
    op.call(x, x)
}

// Function object for equality

#[derive(Default)]
pub struct Equal<T>(PhantomData<T>)
where
    T: Regular;

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

impl<T> Procedure for (Equal<T>, Z0)
where
    T: Regular,
{
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

impl<T0, T1> Regular for Pair<T0, T1>
where
    T0: Regular,
    T1: Regular,
    T0::UnderlyingType: Regular,
    T1::UnderlyingType: Regular,
{
    type UnderlyingType = Pair<T0::UnderlyingType, T1::UnderlyingType>;
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

impl<T0, T1, T2> Regular for Triple<T0, T1, T2>
where
    T0: Regular,
    T1: Regular,
    T2: Regular,
    T0::UnderlyingType: Regular,
    T1::UnderlyingType: Regular,
    T2::UnderlyingType: Regular,
{
    type UnderlyingType = Triple<T0::UnderlyingType, T1::UnderlyingType, T2::UnderlyingType>;
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

pub trait Transformation<Domain>: Fn(Domain) -> Domain {
    type DistanceType: Integer;
}

pub fn power_unary<Domain, F, N>(mut x: Domain, mut n: N, f: &F) -> Domain
where
    F: Transformation<Domain>,
    N: Integer,
{
    // Precondition:
    // $n \geq 0 \wedge (\forall i \in N)\,0 < i \leq n \Rightarrow f^i(x)$ is defined
    while n != N::zero() {
        n = n - N::one();
        x = f(x);
    }
    x
}

pub fn distance<Domain, F>(mut x: Domain, y: &Domain, f: &F) -> F::DistanceType
where
    F: Transformation<Domain>,
    Domain: Regular,
{
    // Precondition: $y$ is reachable from $x$ under $f$
    let mut n = F::DistanceType::zero();
    while x != *y {
        x = f(x);
        n = n + F::DistanceType::one();
    }
    n
}

pub trait UnaryPredicate<Domain> {
    fn call(&self, x: &Domain) -> bool;
}

pub fn collision_point<Domain, F, P>(x: Domain, f: &F, p: &P) -> Domain
where
    Domain: Regular,
    F: Transformation<Domain>,
    P: UnaryPredicate<Domain>,
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    if !p.call(&x) {
        return x;
    }
    let mut slow = x.clone(); // $slow = f^0(x)$
    let mut fast = f(x); // $fast = f^1(x)$
                         // $n \gets 0$ (completed iterations)
    while fast != slow {
        // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
        slow = f(slow); // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 1}(x)$
        if !p.call(&fast) {
            return fast;
        }
        fast = f(fast); // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 2}(x)$
        if !p.call(&fast) {
            return fast;
        }
        fast = f(fast); // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 3}(x)$
                        // $n \gets n + 1$
    }
    fast // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
         // Postcondition: return value is terminal point or collision point
}

pub fn terminating<Domain, F, P>(x: Domain, f: &F, p: &P) -> bool
where
    Domain: Regular,
    F: Transformation<Domain>,
    P: UnaryPredicate<Domain>,
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    !p.call(&collision_point(x, f, p))
}

pub fn collision_point_nonterminating_orbit<Domain, F>(x: Domain, f: &F) -> Domain
where
    Domain: Regular,
    F: Transformation<Domain>,
{
    let mut slow = x.clone(); // $slow = f^0(x)$
    let mut fast = f(x); // $fast = f^1(x)$
                         // $n \gets 0$ (completed iterations)
    while fast != slow {
        // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
        slow = f(slow); // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 1}(x)$
        fast = f(fast); // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 2}(x)$
        fast = f(fast); // $slow = f^{n+1}(x) \wedge fast = f^{2 n + 3}(x)$
                        // $n \gets n + 1$
    }
    fast // $slow = f^n(x) \wedge fast = f^{2 n + 1}(x)$
         // Postcondition: return value is collision point
}

pub fn circular_nonterminating_orbit<Domain, F>(x: &Domain, f: &F) -> bool
where
    Domain: Regular,
    F: Transformation<Domain>,
{
    x == &f(collision_point_nonterminating_orbit(x.clone(), f))
}

pub fn circular<Domain, F, P>(x: &Domain, f: &F, p: &P) -> bool
where
    Domain: Regular,
    F: Transformation<Domain>,
    P: UnaryPredicate<Domain>,
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    let y = collision_point(x.clone(), f, p);
    p.call(&y) && x == &f(y)
}

pub fn convergent_point<Domain, F>(mut x0: Domain, mut x1: Domain, f: &F) -> Domain
where
    Domain: Regular,
    F: Transformation<Domain>,
{
    // Precondition: $(\exists n \in \func{DistanceType}(F))\,n \geq 0 \wedge f^n(x0) = f^n(x1)$
    while x0 != x1 {
        x0 = f(x0);
        x1 = f(x1);
    }
    x0
}

pub fn connection_point_nonterminating_orbit<Domain, F>(x: Domain, f: &F) -> Domain
where
    Domain: Regular,
    F: Transformation<Domain>,
{
    convergent_point(x.clone(), f(collision_point_nonterminating_orbit(x, f)), f)
}

pub fn connection_point<Domain, F, P>(x: Domain, f: &F, p: &P) -> Domain
where
    Domain: Regular,
    F: Transformation<Domain>,
    P: UnaryPredicate<Domain>,
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    let y = collision_point(x.clone(), f, p);
    if !p.call(&y) {
        return y;
    }
    convergent_point(x, f(y), f)
}

// Exercise 2.3:

pub fn convergent_point_guarded<Domain, F>(
    mut x0: Domain,
    mut x1: Domain,
    y: &Domain,
    f: &F,
) -> Domain
where
    Domain: Regular,
    F: Transformation<Domain>,
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

pub fn orbit_structure_nonterminating_orbit<Domain, F>(
    x: Domain,
    f: &F,
) -> Triple<F::DistanceType, F::DistanceType, Domain>
where
    Domain: Regular,
    F: Transformation<Domain>,
{
    let y = connection_point_nonterminating_orbit(x.clone(), f);
    Triple::new(distance(x, &y, f), distance(f(y.clone()), &y, f), y)
}

pub fn orbit_structure<Domain, F, P>(
    x: Domain,
    f: &F,
    p: &P,
) -> Triple<F::DistanceType, F::DistanceType, Domain>
where
    Domain: Regular,
    F: Transformation<Domain>,
    P: UnaryPredicate<Domain>,
{
    // Precondition: $p(x) \Leftrightarrow \text{$f(x)$ is defined}$
    let y = connection_point(x.clone(), f, p);
    let m = distance(x, &y, f);
    let mut n = F::DistanceType::zero();
    if p.call(&y) {
        n = distance(f(y.clone()), &y, f);
    }
    // Terminating: $m = h - 1 \wedge n = 0$
    // Otherwise:   $m = h \wedge n = c - 1$
    Triple::new(m, n, y)
}

//
//  Chapter 3. Associative operations
//

pub fn power_left_associated<I, Op, Domain>(a: Domain, n: I, op: &Op) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
    Domain: Regular,
{
    // Precondition: $n > 0$
    if n == I::one() {
        return a;
    }
    op.call(&power_left_associated(a.clone(), n - I::one(), op), &a)
}

pub fn power_right_associated<I, Op, Domain>(a: Domain, n: I, op: &Op) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
    Domain: Regular,
{
    // Precondition: $n > 0$
    if n == I::one() {
        return a;
    }
    op.call(&a.clone(), &power_right_associated(a, n - I::one(), op))
}

pub fn power_0<I, Op, Domain>(a: Domain, n: I, op: &Op) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
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

pub fn power_1<I, Op, Domain>(a: Domain, n: I, op: &Op) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
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

pub fn power_accumulate_0<I, Op, Domain>(mut r: Domain, a: &Domain, n: I, op: &Op) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
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

pub fn power_accumulate_1<I, Op, Domain>(mut r: Domain, a: &Domain, n: I, op: &Op) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
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

pub fn power_accumulate_2<I, Op, Domain>(mut r: Domain, a: &Domain, n: I, op: &Op) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
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

pub fn power_accumulate_3<I, Op, Domain>(mut r: Domain, mut a: Domain, mut n: I, op: &Op) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
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

pub fn power_accumulate_4<I, Op, Domain>(mut r: Domain, mut a: Domain, mut n: I, op: &Op) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
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

pub fn power_accumulate_positive_0<I, Op, Domain>(
    mut r: Domain,
    mut a: Domain,
    mut n: I,
    op: &Op,
) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
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

pub fn power_accumulate_5<I, Op, Domain>(r: Domain, a: Domain, n: I, op: &Op) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
{
    // Precondition: $\func{associative}(op) \wedge n \geq 0$
    if n == I::zero() {
        return r;
    }
    power_accumulate_positive_0(r, a, n, op)
}

pub fn power_2<I, Op, Domain>(a: Domain, n: I, op: &Op) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
    Domain: Regular,
{
    // Precondition: $\func{associative}(op) \wedge n > 0$
    power_accumulate_5(a.clone(), a, n - I::one(), op)
}

pub fn power_3<I, Op, Domain>(mut a: Domain, mut n: I, op: &Op) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
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

pub fn power_accumulate_positive<I, Op, Domain>(
    mut r: Domain,
    mut a: Domain,
    mut n: I,
    op: &Op,
) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
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

pub fn power_accumulate<I, Op, Domain>(r: Domain, a: Domain, n: I, op: &Op) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
{
    // Precondition: $\func{associative}(op) \wedge \neg \func{negative}(n)$
    if zero(&n) {
        return r;
    }
    power_accumulate_positive(r, a, n, op)
}

pub fn power<I, Op, Domain>(mut a: Domain, mut n: I, op: &Op) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
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

pub fn power_4<I, Op, Domain>(a: Domain, n: I, op: &Op, id: Domain) -> Domain
where
    I: Integer,
    Op: BinaryOperation<Domain>,
{
    // Precondition: $\func{associative}(op) \wedge \neg \func{negative}(n)$
    if zero(&n) {
        return id;
    }
    power(a, n, op)
}

pub fn fibonacci_matrix_multiply<I>(x: &Pair<I, I>, y: &Pair<I, I>) -> Pair<I, I>
where
    I: Integer,
{
    Pair::new(
        x.m0.clone() * (y.m1.clone() + y.m0.clone()) + x.m1.clone() * y.m0.clone(),
        x.m0.clone() * y.m0.clone() + x.m1.clone() * y.m1.clone(),
    )
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
        &fibonacci_matrix_multiply,
    )
    .m0
}

//
//  Chapter 4. Linear orderings
//

// Exercise 4.1: Give an example of a relation that is neither strict nor reflexive
// Exercise 4.2: Give an example of a symmetric relation that is not transitive
// Exercise 4.3: Give an example of a symmetric relation that is not reflexive

pub trait Relation {
    type Domain;
    fn call(&self, x: &Self::Domain, y: &Self::Domain) -> bool;
}

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

pub struct Converse<R>
where
    R: Relation,
{
    r: R,
}

impl<R> Converse<R>
where
    R: Relation,
{
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

pub struct ComplementOfConverse<R>
where
    R: Relation,
{
    r: R,
}

impl<R> ComplementOfConverse<R>
where
    R: Relation,
{
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

pub struct SymmetricComplement<R>
where
    R: Relation,
{
    r: R,
}

impl<R> SymmetricComplement<R>
where
    R: Relation,
{
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

#[derive(Default)]
pub struct Less<T>(PhantomData<T>)
where
    T: TotallyOrdered;

impl<T> Relation for Less<T>
where
    T: TotallyOrdered,
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

#[derive(Default)]
pub struct Plus<T>(PhantomData<T>);

impl<T> BinaryOperation<T> for Plus<T>
where
    T: AdditiveSemigroup,
{
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

pub trait MultiplicativeSemigroup {
    fn mul(&self, y: &Self) -> Self;
}

#[derive(Default)]
pub struct Multiplies<T>(PhantomData<T>);

impl<T> BinaryOperation<T> for Multiplies<T>
where
    T: MultiplicativeSemigroup,
{
    fn call(&self, x: &T, y: &T) -> T {
        x.mul(y)
    }
}

impl<T> Procedure for (Multiplies<T>, Z0) {
    type InputType = T;
}

pub trait SemigroupOperation<Domain>: BinaryOperation<Domain> {}
impl<T, Domain> SemigroupOperation<Domain> for T where T: BinaryOperation<Domain> {}

pub struct MultipliesTransformation<Op, Domain>
where
    Op: SemigroupOperation<Domain>,
{
    x: Domain,
    op: Op,
}

impl<Op, Domain> MultipliesTransformation<Op, Domain>
where
    Op: SemigroupOperation<Domain>,
{
    pub fn new(x: Domain, op: Op) -> Self {
        Self { x, op }
    }
    pub fn call(&self, y: &Domain) -> Domain {
        self.op.call(&self.x, y)
    }
}

impl<Op, Domain> Procedure for (MultipliesTransformation<Op, Domain>, Z0)
where
    Op: SemigroupOperation<Domain>,
{
    type InputType = Domain;
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

pub fn remainder<Domain, Op>(a: &Domain, b: &Domain, rem: &Op) -> Domain
where
    Op: BinaryOperation<Domain>,
    Domain: ArchimedeanGroup,
{
    // Precondition: $b \neq 0$
    let mut r;
    if *a < Domain::zero() {
        if *b < Domain::zero() {
            r = rem.call(&a.neg(), &b.neg()).neg();
        } else {
            r = rem.call(&a.neg(), &b);
            if r != Domain::zero() {
                r = b.sub(&r);
            }
        }
    } else if *b < Domain::zero() {
        r = rem.call(&a, &b.neg());
        if r != Domain::zero() {
            r = b.add(&r);
        }
    } else {
        r = rem.call(&a, &b);
    }
    r
}

pub fn quotient_remainder<Domain, F>(
    a: &Domain,
    b: &Domain,
    quo_rem: &F,
) -> Pair<Domain::QuotientType, Domain>
where
    F: Fn(&Domain, &Domain) -> Pair<Domain::QuotientType, Domain>,
    Domain: ArchimedeanGroup,
    Domain::QuotientType: AdditiveGroup,
{
    // Precondition: $b \neq 0$
    let mut q_r;
    if *a < Domain::zero() {
        if *b < Domain::zero() {
            q_r = quo_rem(&a.neg(), &b.neg());
            q_r.m1 = q_r.m1.neg();
        } else {
            q_r = quo_rem(&a.neg(), &b);
            if q_r.m1 != Domain::zero() {
                q_r.m1 = b.sub(&q_r.m1);
                q_r.m0 = successor(q_r.m0);
            }
            q_r.m0 = q_r.m0.neg();
        }
    } else if *b < Domain::zero() {
        q_r = quo_rem(&a, &b.neg());
        if q_r.m1 != AdditiveMonoid::zero() {
            q_r.m1 = b.add(&q_r.m1);
            q_r.m0 = successor(q_r.m0);
        }
        q_r.m0 = q_r.m0.neg();
    } else {
        q_r = quo_rem(a, b);
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

pub trait Readable {
    type ValueType: Regular;
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
    P: UnaryPredicate<I::ValueType>,
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
    P: UnaryPredicate<I::ValueType>,
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
    P: UnaryPredicate<I::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    *l == find_if_not(f, l, p)
}

pub fn none<I, P>(f: I, l: &I, p: &P) -> bool
where
    I: Readable + Iterator,
    P: UnaryPredicate<I::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    *l == find_if(f, l, p)
}

pub fn not_all<I, P>(f: I, l: &I, p: &P) -> bool
where
    I: Readable + Iterator,
    P: UnaryPredicate<I::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    !all(f, l, p)
}

pub fn some<I, P>(f: I, l: &I, p: &P) -> bool
where
    I: Readable + Iterator,
    P: UnaryPredicate<I::ValueType>,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    !none(f, l, p)
}

pub fn count_if<I, P, J>(mut f: I, l: &I, p: &P, mut j: J) -> J
where
    I: Readable + Iterator,
    P: UnaryPredicate<I::ValueType>,
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
    P: UnaryPredicate<I::ValueType>,
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
    P: UnaryPredicate<I::ValueType>,
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
    P: UnaryPredicate<I::ValueType>,
    I::DistanceType: Iterator,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    count_if_not(f, l, p, I::DistanceType::zero())
}

pub fn reduce_nonempty<I, Op, F, Domain>(mut f: I, l: &I, op: &Op, fun: &F) -> Domain
where
    I: Iterator,
    Op: BinaryOperation<Domain>,
    F: Fn(&I) -> &Domain,
    Domain: Regular,
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

pub fn reduce_nonempty_1<I, Op, Domain>(mut f: I, l: &I, op: &Op) -> Domain
where
    I: Readable<ValueType = Domain> + Iterator,
    Op: BinaryOperation<Domain>,
    Domain: Regular,
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

pub fn reduce<I, Op, F, Domain>(f: I, l: &I, op: &Op, fun: &F, z: &Domain) -> Domain
where
    I: Iterator,
    Op: BinaryOperation<Domain>,
    F: Fn(&I) -> &Domain,
    Domain: Regular,
{
    // Precondition: $\property{bounded\_range}(f, l)$
    // Precondition: $\property{partially\_associative}(op)$
    // Precondition: $(\forall x \in [f, l))\,fun(x)$ is defined
    if f == *l {
        return z.clone();
    }
    reduce_nonempty(f, l, op, fun)
}

pub fn reduce_1<I, Op, Domain>(f: I, l: &I, op: &Op, z: &Domain) -> Domain
where
    I: Readable<ValueType = Domain> + Iterator,
    Op: BinaryOperation<Domain>,
    Domain: Regular,
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    // Precondition: $\property{partially\_associative}(op)$
    if f == *l {
        return z.clone();
    }
    reduce_nonempty_1(f, l, op)
}

pub fn reduce_nonzeroes<I, Op, F, Domain>(mut f: I, l: &I, op: &Op, fun: &F, z: &Domain) -> Domain
where
    I: Iterator,
    Op: BinaryOperation<Domain>,
    F: Fn(&I) -> &Domain,
    Domain: Regular,
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

pub fn reduce_nonzeroes_1<I, Op, Domain>(mut f: I, l: &I, op: &Op, z: &Domain) -> Domain
where
    I: Readable<ValueType = Domain> + Iterator,
    Op: BinaryOperation<Domain>,
    Domain: Regular,
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

pub fn find_if_unguarded<I, P, Domain>(mut f: I, p: &P) -> I
where
    I: Readable<ValueType = Domain> + Iterator,
    P: UnaryPredicate<Domain>,
    Domain: Regular,
{
    // Precondition:
    // $(\exists l)\,\func{readable\_bounded\_range}(f, l) \wedge \func{some}(f, l, p)$
    while !p.call(f.source()) {
        f = f.successor();
    }
    f
    // Postcondition: $p(\func{source}(f))$
}

pub fn find_if_not_unguarded<I, P, Domain>(mut f: I, p: &P) -> I
where
    I: Readable<ValueType = Domain> + Iterator,
    P: UnaryPredicate<Domain>,
    Domain: Regular,
{
    // Let $l$ be the end of the implied range starting with $f$
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{not\_all}(f, l, p)$
    while p.call(f.source()) {
        f = f.successor();
    }
    f
}

pub fn find_mismatch<I0, I1, R, Domain>(
    mut f0: I0,
    l0: &I0,
    mut f1: I1,
    l1: &I1,
    r: &R,
) -> Pair<I0, I1>
where
    I0: Readable<ValueType = Domain> + Iterator,
    I1: Readable<ValueType = Domain> + Iterator,
    R: Relation<Domain = Domain>,
    Domain: Regular,
{
    // Precondition: $\func{readable\_bounded\_range}(f0, l0)$
    // Precondition: $\func{readable\_bounded\_range}(f1, l1)$
    while f0 != *l0 && f1 != *l1 && r.call(f0.source(), f1.source()) {
        f0 = f0.successor();
        f1 = f1.successor();
    }
    Pair::new(f0, f1)
}

pub fn find_adjacent_mismatch<I, R, Domain>(mut f: I, l: &I, r: &R) -> I
where
    I: Readable<ValueType = Domain> + Iterator,
    R: Relation<Domain = Domain>,
    Domain: Regular,
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

pub fn relation_preserving<I, R, Domain>(f: I, l: &I, r: &R) -> bool
where
    I: Readable<ValueType = Domain> + Iterator,
    R: Relation<Domain = Domain>,
    Domain: Regular,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    *l == find_adjacent_mismatch(f, l, r)
}

pub fn strictly_increasing_range<I, R, Domain>(f: I, l: &I, r: &R) -> bool
where
    I: Readable<ValueType = Domain> + Iterator,
    R: Relation<Domain = Domain>,
    Domain: Regular,
{
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{weak\_ordering}(r)$
    relation_preserving(f, l, r)
}

pub fn increasing_range<I, R, Domain>(f: I, l: &I, r: &R) -> bool
where
    I: Readable<ValueType = Domain> + Iterator,
    R: Relation<Domain = Domain> + Regular,
    Domain: Regular,
{
    // Precondition:
    // $\func{readable\_bounded\_range}(f, l) \wedge \func{weak\_ordering}(r)$
    relation_preserving(f, l, &ComplementOfConverse::new(r.clone()))
}

pub fn partitioned<I, P, Domain>(f: I, l: &I, p: &P) -> bool
where
    I: Readable<ValueType = Domain> + Iterator,
    P: UnaryPredicate<Domain>,
    Domain: Regular,
{
    // Precondition: $\func{readable\_bounded\_range}(f, l)$
    *l == find_if_not(find_if(f, l, p), l, p)
}

// Exercise 6.6: partitioned_n

pub trait ForwardIterator: Iterator {}
impl<T> ForwardIterator for T where T: Iterator {}

pub fn find_adjacent_mismatch_forward<I, R, Domain>(mut f: I, l: &I, r: &R) -> I
where
    I: Readable<ValueType = Domain> + ForwardIterator,
    R: Relation<Domain = Domain>,
    Domain: Regular,
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

pub fn partition_point_n<I, P, Domain>(mut f: I, mut n: I::DistanceType, p: &P) -> I
where
    I: Readable<ValueType = Domain> + ForwardIterator,
    P: UnaryPredicate<Domain>,
    Domain: Regular,
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

pub fn partition_point<I, P, Domain>(f: I, l: I, p: &P) -> I
where
    I: Readable<ValueType = Domain> + ForwardIterator,
    P: UnaryPredicate<Domain>,
    Domain: Regular,
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

impl<'a, R> UnaryPredicate<R::Domain> for LowerBoundPredicate<'a, R>
where
    R: Relation,
{
    fn call(&self, x: &R::Domain) -> bool {
        !self.r.call(x, self.a)
    }
}

pub fn lower_bound_n<I, R, Domain>(f: I, n: I::DistanceType, a: &I::ValueType, r: &R) -> I
where
    I: Readable<ValueType = Domain> + ForwardIterator,
    R: Relation<Domain = Domain> + Regular,
    Domain: Regular,
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

impl<'a, R> UnaryPredicate<R::Domain> for UpperBoundPredicate<'a, R>
where
    R: Relation,
{
    fn call(&self, x: &R::Domain) -> bool {
        self.r.call(self.a, x)
    }
}

pub fn upper_bound_n<I, R, Domain>(f: I, n: I::DistanceType, a: &I::ValueType, r: &R) -> I
where
    I: Readable<ValueType = Domain> + ForwardIterator,
    R: Relation<Domain = Domain> + Regular,
    Domain: Regular,
{
    // Precondition:
    // $\property{weak\_ordering(r)} \wedge \property{increasing\_counted\_range}(f, n, r)$
    let p = UpperBoundPredicate::new(a, r.clone());
    partition_point_n(f, n, &p)
}

// Exercise 6.7: equal_range

pub trait BidirectionalIterator: ForwardIterator {
    fn predecessor(&self) -> Self;
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

pub fn find_backward_if<I, P, Domain>(f: &I, mut l: I, p: &P) -> I
where
    I: Readable<ValueType = Domain> + BidirectionalIterator,
    P: UnaryPredicate<Domain>,
    Domain: Regular,
{
    // Precondition: $(f, l] \text{ is a readable bounded half-open on left range}$
    while l != *f && !p.call(l.predecessor().source()) {
        l = l.predecessor();
    }
    l
}

pub fn find_backward_if_not<I, P, Domain>(f: &I, mut l: I, p: &P) -> I
where
    I: Readable<ValueType = Domain> + BidirectionalIterator,
    P: UnaryPredicate<Domain>,
    Domain: Regular,
{
    // Precondition: $(f, l] \text{ is a readable bounded half-open on left range}$
    while l != *f && p.call(l.predecessor().source()) {
        l = l.predecessor();
    }
    l
}

// Exercise 6.8: optimized find_backward_if

// Exercise 6.9: palindrome predicate

pub fn find_backward_if_unguarded<I, P, Domain>(mut l: I, p: &P) -> I
where
    I: Readable<ValueType = Domain> + BidirectionalIterator,
    P: UnaryPredicate<Domain>,
    Domain: Regular,
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

pub fn find_backward_if_not_unguarded<I, P, Domain>(mut l: I, p: &P) -> I
where
    I: Readable<ValueType = Domain> + BidirectionalIterator,
    P: UnaryPredicate<Domain>,
    Domain: Regular,
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

pub fn lexicographical_equivalent<I0, I1, R, Domain>(
    f0: I0,
    l0: &I0,
    f1: I1,
    l1: &I1,
    r: &R,
) -> bool
where
    I0: Readable<ValueType = Domain> + Iterator,
    I1: Readable<ValueType = Domain> + Iterator,
    R: Relation<Domain = Domain>,
    Domain: Regular,
{
    // Precondition: $\property{readable\_bounded\_range}(f0, l0)$
    // Precondition: $\property{readable\_bounded\_range}(f1, l1)$
    // Precondition: $\property{equivalence}(r)$
    let p = find_mismatch(f0, l0, f1, l1, r);
    p.m0 == *l0 && p.m1 == *l1
}

pub fn lexicographical_equal<I0, I1, Domain>(f0: I0, l0: &I0, f1: I1, l1: &I1) -> bool
where
    I0: Readable<ValueType = Domain> + Iterator,
    I1: Readable<ValueType = Domain> + Iterator,
    Domain: Regular,
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

pub fn bifurcate_equivalent_nonempty<C0, C1, R, Domain>(c0: &C0, c1: &C1, r: &R) -> bool
where
    C0: Readable<ValueType = Domain> + BifurcateCoordinate,
    C1: Readable<ValueType = Domain> + BifurcateCoordinate,
    R: Relation<Domain = Domain>,
    Domain: Regular,
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

pub fn bifurcate_equivalent<C0, C1, R, Domain>(mut c0: C0, mut c1: C1, r: &R) -> bool
where
    C0: Readable<ValueType = Domain> + BidirectionalBifurcateCoordinate,
    C1: Readable<ValueType = Domain> + BidirectionalBifurcateCoordinate,
    R: Relation<Domain = Domain>,
    Domain: Regular,
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

pub fn bifurcate_equal<C0, C1, Domain>(c0: C0, c1: C1) -> bool
where
    C0: Readable<ValueType = Domain> + BidirectionalBifurcateCoordinate,
    C1: Readable<ValueType = Domain> + BidirectionalBifurcateCoordinate,
    Domain: Regular,
{
    bifurcate_equivalent(c0, c1, &Equal::default())
}

pub fn lexicographical_compare<I0, I1, R, Domain>(
    mut f0: I0,
    l0: &I0,
    mut f1: I1,
    l1: &I1,
    r: &R,
) -> bool
where
    I0: Readable<ValueType = Domain> + Iterator,
    I1: Readable<ValueType = Domain> + Iterator,
    R: Relation<Domain = Domain>,
    Domain: Regular,
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

pub fn lexicographical_less<I0, I1, Domain>(f0: I0, l0: &I0, f1: I1, l1: &I1) -> bool
where
    I0: Readable<ValueType = Domain> + Iterator,
    I1: Readable<ValueType = Domain> + Iterator,
    Domain: Regular + TotallyOrdered,
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

pub trait Compare3Way<T> {
    fn call(&self, a: &T, b: &T) -> i32;
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

impl<R> Compare3Way<R::Domain> for Comparator3Way<R>
where
    R: Relation,
{
    fn call(&self, a: &R::Domain, b: &R::Domain) -> i32 {
        if self.r.call(a, b) {
            return 1;
        }
        if self.r.call(b, a) {
            return -1;
        }
        0
    }
}

pub fn lexicographical_compare_3way<I0, I1, F, R, Domain>(
    mut f0: I0,
    l0: &I0,
    mut f1: I1,
    l1: &I1,
    comp: &F,
) -> i32
where
    I0: Readable<ValueType = Domain> + Iterator,
    I1: Readable<ValueType = Domain> + Iterator,
    F: Compare3Way<Domain>,
    R: Relation<Domain = Domain>,
    Domain: Regular,
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

pub fn bifurcate_compare_nonempty<C0, C1, F, Domain>(c0: &C0, c1: &C1, comp: &F) -> i32
where
    C0: Readable<ValueType = Domain> + BifurcateCoordinate,
    C1: Readable<ValueType = Domain> + BifurcateCoordinate,
    F: Compare3Way<Domain>,
    Domain: Regular,
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
    C0::ValueType: Regular,
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
    C0::ValueType: Regular + TotallyOrdered,
{
    // Precondition: $\property{readable\_tree}(c0) \wedge
    //                \property{readable\_tree}(c1)
    bifurcate_compare(c0, c1, &Less::default())
}

#[derive(Default)]
pub struct AlwaysFalse<T>(PhantomData<T>);

impl<T> Relation for AlwaysFalse<T> {
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

template<typename I>
    requires(ForwardIterator(I))
void advance_tail(I& t, I& f)
{
    // Precondition: $\func{successor}(f)\text{ is defined}$
    t = f;
    f = successor(f);
}

template<typename S>
    requires(ForwardLinker(S))
struct linker_to_tail
{
    typedef IteratorType(S) I;
    S set_link;
    linker_to_tail(const S& set_link) : set_link(set_link) { }
    void operator()(I& t, I& f)
    {
        // Precondition: $\func{successor}(f)\text{ is defined}$
        set_link(t, f);
        advance_tail(t, f);
    }
};

template<typename I>
    requires(ForwardIterator(I))
I find_last(I f, I l)
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge f \neq l$
    I t;
    do
        advance_tail(t, f);
    while (f != l);
    return t;
}

template<typename I, typename S, typename Pred>
    requires(ForwardLinker(S) && I == IteratorType(S) &&
        UnaryPseudoPredicate(Pred) && I == Domain(Pred))
pair< pair<I, I>, pair<I, I> >
split_linked(I f, I l, Pred p, S set_link)
{
    // Precondition: $\property{bounded\_range}(f, l)$
    typedef pair<I, I> P;
    linker_to_tail<S> link_to_tail(set_link);
    I h0 = l; I t0 = l;
    I h1 = l; I t1 = l;
    if (f == l)                              goto s4;
    if (p(f)) { h1 = f; advance_tail(t1, f); goto s1; }
    else      { h0 = f; advance_tail(t0, f); goto s0; }
s0: if (f == l)                              goto s4;
    if (p(f)) { h1 = f; advance_tail(t1, f); goto s3; }
    else      {         advance_tail(t0, f); goto s0; }
s1: if (f == l)                              goto s4;
    if (p(f)) {         advance_tail(t1, f); goto s1; }
    else      { h0 = f; advance_tail(t0, f); goto s2; }
s2: if (f == l)                              goto s4;
    if (p(f)) {         link_to_tail(t1, f); goto s3; }
    else      {         advance_tail(t0, f); goto s2; }
s3: if (f == l)                              goto s4;
    if (p(f)) {         advance_tail(t1, f); goto s3; }
    else      {         link_to_tail(t0, f); goto s2; }
s4: return pair<P, P>(P(h0, t0), P(h1, t1));
}

// Exercise 8.1: Explain the postcondition of split_linked


template<typename I, typename S, typename R>
    requires(ForwardLinker(S) && I == IteratorType(S) &&
        PseudoRelation(R) && I == Domain(R))
triple<I, I, I>
combine_linked_nonempty(I f0, I l0, I f1, I l1, R r, S set_link)
{
    // Precondition: $\property{bounded\_range}(f0, l0) \wedge
    //                \property{bounded\_range}(f1, l1)$
    // Precondition: $f0 \neq l0 \wedge f1 \neq l1 \wedge
    //                \property{disjoint}(f0, l0, f1, l1)$
    typedef triple<I, I, I> T;
    linker_to_tail<S> link_to_tail(set_link);
    I h; I t;
    if (r(f1, f0)) { h = f1; advance_tail(t, f1); goto s1; }
    else           { h = f0; advance_tail(t, f0); goto s0; }
s0: if (f0 == l0)                                 goto s2;
    if (r(f1, f0)) {         link_to_tail(t, f1); goto s1; }
    else           {         advance_tail(t, f0); goto s0; }
s1: if (f1 == l1)                                 goto s3;
    if (r(f1, f0)) {         advance_tail(t, f1); goto s1; }
    else           {         link_to_tail(t, f0); goto s0; }
s2: set_link(t, f1); return T(h, t, l1);
s3: set_link(t, f0); return T(h, t, l0);
}

// Exercise 8.2: combine_linked


template<typename I, typename S>
    requires(ForwardLinker(S) && I == IteratorType(S))
struct linker_to_head
{
    S set_link;
    linker_to_head(const S& set_link) : set_link(set_link) { }
    void operator()(I& h, I& f)
    {
        // Precondition: $\func{successor}(f)$ is defined
        IteratorType(S) tmp = successor(f);
        set_link(f, h);
        h = f;
        f = tmp;
    }
};

template<typename I, typename S>
    requires(ForwardLinker(S) && I == IteratorType(S))
I reverse_append(I f, I l, I h, S set_link)
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge h \notin [f, l)$
    linker_to_head<I, S> link_to_head(set_link);
    while (f != l) link_to_head(h, f);
    return h;
}

template<typename I, typename P>
    requires(Readable(I) &&
        Predicate(P) && ValueType(I) == Domain(P))
struct predicate_source
{
    P p;
    predicate_source(const P& p) : p(p) { }
    bool operator()(I i)
    {
        return p(source(i));
    }
};

template<typename I, typename S, typename P>
    requires(ForwardLinker(S) && I == IteratorType(S) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair< pair<I, I>, pair<I, I> >
partition_linked(I f, I l, P p, S set_link)
{
    // Precondition: $\property{bounded\_range}(f, l)$
    predicate_source<I, P> ps(p);
    return split_linked(f, l, ps, set_link);
}

template<typename I0, typename I1, typename R>
    requires(Readable(I0) && Readable(I1) &&
        ValueType(I0) == ValueType(I1) &&
        Relation(R) && ValueType(I0) == Domain(R))
struct relation_source
{
    R r;
    relation_source(const R& r) : r(r) { }
    bool operator()(I0 i0, I1 i1)
    {
        return r(source(i0), source(i1));
    }
};

template<typename I, typename S, typename R>
    requires(Readable(I) &&
        ForwardLinker(S) && I == IteratorType(S) &&
        Relation(R) && ValueType(I) == Domain(R))
pair<I, I> merge_linked_nonempty(I f0, I l0, I f1, I l1,
                                 R r, S set_link)
{
    // Precondition: $f0 \neq l0 \wedge f1 \neq l1$
    // Precondition: $\property{increasing\_range}(f0, l0, r)$
    // Precondition: $\property{increasing\_range}(f1, l1, r)$
    relation_source<I, I, R> rs(r);
    triple<I, I, I> t = combine_linked_nonempty(f0, l0, f1, l1,
                                                rs, set_link);
    set_link(find_last(t.m1, t.m2), l1);
    return pair<I, I>(t.m0, l1);
}

template<typename I, typename S, typename R>
    requires(Readable(I) &&
        ForwardLinker(S) && I == IteratorType(S) &&
        Relation(R) && ValueType(I) == Domain(R))
pair<I, I> sort_linked_nonempty_n(I f, DistanceType(I) n,
                                  R r, S set_link)
{
    // Precondition: $\property{counted\_range}(f, n) \wedge
    //                n > 0 \wedge \func{weak\_ordering}(r)$
    typedef DistanceType(I) N;
    typedef pair<I, I> P;
    if (n == N(1)) return P(f, successor(f));
    N h = half_nonnegative(n);
    P p0 = sort_linked_nonempty_n(f, h, r, set_link);
    P p1 = sort_linked_nonempty_n(p0.m1, n - h, r, set_link);
    return merge_linked_nonempty(p0.m0, p0.m1,
                                 p1.m0, p1.m1, r, set_link);
}

// Exercise 8.3: Complexity of sort_linked_nonempty_n


// Exercise 8.4: unique


template<typename C>
     requires(EmptyLinkedBifurcateCoordinate(C))
void tree_rotate(C& curr, C& prev)
{
    // Precondition: $\neg \func{empty}(curr)$
    C tmp = left_successor(curr);
    set_left_successor(curr, right_successor(curr));
    set_right_successor(curr, prev);
    if (empty(tmp)) { prev = tmp; return; }
    prev = curr;
    curr = tmp;
}

template<typename C, typename Proc>
    requires(EmptyLinkedBifurcateCoordinate(C) &&
        Procedure(Proc) && Arity(Proc) == 1 &&
        C == InputType(Proc, 0))
Proc traverse_rotating(C c, Proc proc)
{
    // Precondition: $\property{tree}(c)$
    if (empty(c)) return proc;
    C curr = c;
    C prev;
    do {
        proc(curr);
        tree_rotate(curr, prev);
    } while (curr != c);
    do {
        proc(curr);
        tree_rotate(curr, prev);
    } while (curr != c);
    proc(curr);
    tree_rotate(curr, prev);
    return proc;
}

// Exercise 8.5: Diagram each state of traverse_rotating
// for a complete binary tree with 7 nodes


template<typename T, typename N>
    requires(Integer(N))
struct counter
{
    N n;
    counter() : n(0) { }
    counter(N n) : n(n) { }
    void operator()(const T&) { n = successor(n); }
};

template<typename C>
    requires(EmptyLinkedBifurcateCoordinate(C))
WeightType(C) weight_rotating(C c)
{
    // Precondition: $\property{tree}(c)$
    typedef WeightType(C) N;
    return traverse_rotating(c, counter<C, N>()).n / N(3);
}

template<typename N, typename Proc>
    requires(Integer(N) &&
        Procedure(Proc) && Arity(Proc) == 1)
struct phased_applicator
{
    N period;
    N phase;
    N n;
    // Invariant: $n, phase \in [0, period)$
    Proc proc;
    phased_applicator(N period, N phase, N n, Proc proc) :
        period(period), phase(phase), n(n), proc(proc) { }
    void operator()(InputType(Proc, 0) x)
    {
        if (n == phase) proc(x);
        n = successor(n);
        if (n == period) n = 0;
    }
};

template<typename C, typename Proc>
    requires(EmptyLinkedBifurcateCoordinate(C) &&
        Procedure(Proc) && Arity(Proc) == 1 &&
        C == InputType(Proc, 0))
Proc traverse_phased_rotating(C c, int phase, Proc proc)
{
    // Precondition: $\property{tree}(c) \wedge 0 \leq phase < 3$
    phased_applicator<int, Proc> applicator(3, phase, 0, proc);
    return traverse_rotating(c, applicator).proc;
}


//
//  Chapter 9. Copying
//


template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O))
void copy_step(I& f_i, O& f_o)
{
    // Precondition: $\func{source}(f_i)$ and $\func{sink}(f_o)$ are defined
    sink(f_o) = source(f_i);
    f_i = successor(f_i);
    f_o = successor(f_o);
}

template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O))
O copy(I f_i, I l_i, O f_o)
{
    // Precondition:
    // $\property{not\_overlapped\_forward}(f_i, l_i, f_o, f_o + (l_i - f_i))$
    while (f_i != l_i) copy_step(f_i, f_o);
    return f_o;
}

template<typename I>
    requires(Writable(I) && Iterator(I))
void fill_step(I& f_o, const ValueType(I)& x)
{
    sink(f_o) = x;
    f_o = successor(f_o);
}

template<typename I>
    requires(Writable(I) && Iterator(I))
I fill(I f, I l, const ValueType(I)& x)
{
    while (f != l) fill_step(f, x);
    return f;
}

template<typename O>
    requires(Writable(O) && Iterator(O) &&
        Integer(ValueType(O)))
O iota(ValueType(O) n, O o) // like APL $\iota$
{
    // Precondition: $\property{writable\_counted\_range}(o, n) \wedge n \geq 0$
    return copy(ValueType(O)(0), n, o);
}

// Useful for testing in conjunction with iota
template<typename I>
    requires(Readable(I) && Iterator(I) &&
        Integer(ValueType(I)))
bool equal_iota(I f, I l, ValueType(I) n = 0)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    while (f != l) {
        if (source(f) != n) return false;
        n = successor(n);
        f = successor(f);
    }
    return true;
}

template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O))
pair<I, O> copy_bounded(I f_i, I l_i, O f_o, O l_o)
{
    // Precondition: $\property{not\_overlapped\_forward}(f_i, l_i, f_o, l_o)$
    while (f_i != l_i && f_o != l_o) copy_step(f_i, f_o);
    return pair<I, O>(f_i, f_o);
}

template<typename N>
    requires(Integer(N))
bool count_down(N& n)
{
    // Precondition: $n \geq 0$
    if (zero(n)) return false;
    n = predecessor(n);
    return true;
}

template<typename I, typename O, typename N>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O) &&
        Integer(N))
pair<I, O> copy_n(I f_i, N n, O f_o)
{
    // Precondition: $\property{not\_overlapped\_forward}(f_i, f_i+n, f_o, f_o+n)$
    while (count_down(n)) copy_step(f_i, f_o);
    return pair<I, O>(f_i, f_o);
}

template<typename I>
    requires(Writable(I) && Iterator(I))
I fill_n(I f, DistanceType(I) n, const ValueType(I)& x)
{
    while (count_down(n)) fill_step(f, x);
    return f;
}

template<typename I, typename O>
    requires(Readable(I) && BidirectionalIterator(I) &&
        Writable(O) && BidirectionalIterator(O) &&
        ValueType(I) == ValueType(O))
void copy_backward_step(I& l_i, O& l_o)
{
    // Precondition: $\func{source}(\property{predecessor}(l_i))$ and
    //               $\func{sink}(\property{predecessor}(l_o))$
    //               are defined
    l_i = predecessor(l_i);
    l_o = predecessor(l_o);
    sink(l_o) = source(l_i);
}

template<typename I, typename O>
    requires(Readable(I) && BidirectionalIterator(I) &&
        Writable(O) && BidirectionalIterator(O) &&
        ValueType(I) == ValueType(O))
O copy_backward(I f_i, I l_i, O l_o)
{
    // Precondition: $\property{not\_overlapped\_backward}(f_i, l_i, l_o-(l_i-f_i), l_o)$
    while (f_i != l_i) copy_backward_step(l_i, l_o);
    return l_o;
}

template<typename I, typename O>
    requires(Readable(I) && BidirectionalIterator(I) &&
        Writable(O) && BidirectionalIterator(O) &&
        ValueType(I) == ValueType(O))
pair<I, O> copy_backward_n(I l_i, DistanceType(I) n, O l_o)
{
    while (count_down(n)) copy_backward_step(l_i, l_o);
    return pair<I, O>(l_i, l_o);
}

template<typename I, typename O>
    requires(Readable(I) && BidirectionalIterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O))
void reverse_copy_step(I& l_i, O& f_o)
{
    // Precondition: $\func{source}(\func{predecessor}(l_i))$ and
    //               $\func{sink}(f_o)$ are defined
    l_i = predecessor(l_i);
    sink(f_o) = source(l_i);
    f_o = successor(f_o);
}

template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && BidirectionalIterator(O) &&
        ValueType(I) == ValueType(O))
void reverse_copy_backward_step(I& f_i, O& l_o)
{
    // Precondition: $\func{source}(f_i)$ and
    //               $\func{sink}(\property{predecessor}(l_o))$ are defined
    l_o = predecessor(l_o);
    sink(l_o) = source(f_i);
    f_i = successor(f_i);
}

template<typename I, typename O>
    requires(Readable(I) && BidirectionalIterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O))
O reverse_copy(I f_i, I l_i, O f_o)
{
    // Precondition: $\property{not\_overlapped}(f_i, l_i, f_o, f_o+(l_i-f_i))$
    while (f_i != l_i) reverse_copy_step(l_i, f_o);
    return f_o;
}

template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && BidirectionalIterator(O) &&
        ValueType(I) == ValueType(O))
O reverse_copy_backward(I f_i, I l_i, O l_o)
{
    // Precondition: $\property{not\_overlapped}(f_i, l_i, l_o-(l_i-f_i), l_o)$
    while (f_i != l_i) reverse_copy_backward_step(f_i, l_o);
    return l_o;
}

template<typename I, typename O, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O) &&
        UnaryPredicate(P) && I == Domain(P))
O copy_select(I f_i, I l_i, O f_t, P p)
{
    // Precondition: $\property{not\_overlapped\_forward}(f_i, l_i, f_t, f_t+n_t)$
    // where $n_t$ is an upper bound for the number of iterators satisfying $p$
    while (f_i != l_i)
        if (p(f_i)) copy_step(f_i, f_t);
        else f_i = successor(f_i);
    return f_t;
}

template<typename I, typename O, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
O copy_if(I f_i, I l_i, O f_t, P p)
{
    // Precondition: same as for $\func{copy\_select}$
    predicate_source<I, P> ps(p);
    return copy_select(f_i, l_i, f_t, ps);
}

template<typename I, typename O_f, typename O_t, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O_f) && Iterator(O_f) &&
        Writable(O_t) && Iterator(O_t) &&
        ValueType(I) == ValueType(O_f) &&
        ValueType(I) == ValueType(O_t) &&
        UnaryPredicate(P) && I == Domain(P))
pair<O_f, O_t> split_copy(I f_i, I l_i, O_f f_f, O_t f_t,
                          P p)
{
    // Precondition: see section 9.3 of Elements of Programming
    while (f_i != l_i)
        if (p(f_i)) copy_step(f_i, f_t);
        else        copy_step(f_i, f_f);
    return pair<O_f, O_t>(f_f, f_t);
}

template<typename I, typename O_f, typename O_t, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O_f) && Iterator(O_f) &&
        Writable(O_t) && Iterator(O_t) &&
        ValueType(I) == ValueType(O_f) &&
        ValueType(I) == ValueType(O_t) &&
        UnaryPredicate(P) && I == Domain(P))
pair<O_f, O_t> split_copy_n(I f_i, DistanceType(I) n_i, O_f f_f, O_t f_t, P p)
{
    // Precondition: see exercise 9.2 of Elements of Programming
    while (count_down(n_i))
        if (p(f_i)) copy_step(f_i, f_t);
        else        copy_step(f_i, f_f);
    return pair<O_f, O_t>(f_f, f_t);
}

template<typename I, typename O_f, typename O_t, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O_f) && Iterator(O_f) &&
        Writable(O_t) && Iterator(O_t) &&
        ValueType(I) == ValueType(O_f) &&
        ValueType(I) == ValueType(O_t) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<O_f, O_t> partition_copy(I f_i, I l_i, O_f f_f, O_t f_t,
                              P p)
{
    // Precondition: same as $\func{split\_copy}$
    predicate_source<I, P> ps(p);
    return split_copy(f_i, l_i, f_f, f_t, ps);
}

template<typename I, typename O_f, typename O_t, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O_f) && Iterator(O_f) &&
        Writable(O_t) && Iterator(O_t) &&
        ValueType(I) == ValueType(O_f) &&
        ValueType(I) == ValueType(O_t) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<O_f, O_t> partition_copy_n(I f_i, DistanceType(I) n,
                                O_f f_f, O_t f_t,
                                P p)
{
    // Precondition: see $\func{partition_copy}$
    predicate_source<I, P> ps(p);
    return split_copy_n(f_i, n, f_f, f_t, ps);
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        Writable(O) && Iterator(O) &&
        BinaryPredicate(R) &&
        ValueType(I0) == ValueType(O) &&
        ValueType(I1) == ValueType(O) &&
        I0 == InputType(R, 1) && I1 == InputType(R, 0))
O combine_copy(I0 f_i0, I0 l_i0, I1 f_i1, I1 l_i1, O f_o, R r)
{
    // Precondition: see section 9.3 of Elements of Programming
    while (f_i0 != l_i0 && f_i1 != l_i1)
        if (r(f_i1, f_i0)) copy_step(f_i1, f_o);
        else               copy_step(f_i0, f_o);
    return copy(f_i1, l_i1, copy(f_i0, l_i0, f_o));
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        Writable(O) && Iterator(O) &&
        BinaryPredicate(R) &&
        ValueType(I0) == ValueType(O) &&
        ValueType(I1) == ValueType(O) &&
        I0 == InputType(R, 1) && I1 = InputType(R, 0))
triple<I0, I1, O> combine_copy_n(I0 f_i0, DistanceType(I0) n_i0,
                                 I1 f_i1, DistanceType(I1) n_i1,
                                 O f_o, R r) {
    // Precondition: see $\func{combine_copy}$
    typedef triple<I0, I1, O> Triple;
    while (true) {
        if (zero(n_i0)) {
            pair<I1, O> p = copy_n(f_i1, n_i1, f_o);
            return Triple(f_i0, p.m0, p.m1);
        }
        if (zero(n_i1)) {
            pair<I0, O> p = copy_n(f_i0, n_i0, f_o);
            return Triple(p.m0, f_i1, p.m1);
        }
        if (r(f_i1, f_i0)) {
            copy_step(f_i1, f_o);
            n_i1 = predecessor(n_i1);
        } else             {
            copy_step(f_i0, f_o);
            n_i0 = predecessor(n_i0);
        }
    }
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && BidirectionalIterator(I0) &&
        Readable(I1) && BidirectionalIterator(I1) &&
        Writable(O) && BidirectionalIterator(O) &&
        BinaryPredicate(R) &&
        ValueType(I0) == ValueType(O) &&
        ValueType(I1) == ValueType(O) &&
        I0 == InputType(R, 1) && I1 == InputType(R, 0))
O combine_copy_backward(I0 f_i0, I0 l_i0, I1 f_i1, I1 l_i1,
                        O l_o, R r)
{
    // Precondition: see section 9.3 of Elements of Programming
    while (f_i0 != l_i0 && f_i1 != l_i1) {
        if (r(predecessor(l_i1), predecessor(l_i0)))
            copy_backward_step(l_i0, l_o);
        else
            copy_backward_step(l_i1, l_o);
    }
    return copy_backward(f_i0, l_i0,
                         copy_backward(f_i1, l_i1, l_o));
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && BidirectionalIterator(I0) &&
        Readable(I1) && BidirectionalIterator(I1) &&
        Writable(O) && BidirectionalIterator(O) &&
        BinaryPredicate(R) &&
        ValueType(I0) == ValueType(O) && ValueType(I1) == ValueType(O) &&
        I0 == InputType(R, 1) && I1 = InputType(R, 0))
triple<I0, I1, O> combine_copy_backward_n(I0 l_i0, DistanceType(I0) n_i0,
                           I1 l_i1, DistanceType(I1) n_i1, O l_o, R r) {
    // Precondition: see $\func{combine\_copy\_backward}$
    typedef triple<I0, I1, O> Triple;
    while (true) {
        if (zero(n_i0)) {
            pair<I1, O> p = copy_backward_n(l_i1, n_i1, l_o);
            return Triple(l_i0, p.m0, p.m1);
        }
        if (zero(n_i1)) {
            pair<I0, O> p = copy_backward_n(l_i0, n_i0, l_o);
            return Triple(p.m0, l_i1, p.m1);
        }
        if (r(predecessor(l_i1), predecessor(l_i0))) {
            copy_backward_step(l_i0, l_o);
            n_i0 = predecessor(n_i0);
        } else {
            copy_backward_step(l_i1, l_o);
            n_i1 = predecessor(n_i1);
        }
    }
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        Writable(O) && Iterator(O) &&
        Relation(R) &&
        ValueType(I0) == ValueType(O) &&
        ValueType(I1) == ValueType(O) &&
        ValueType(I0) == Domain(R))
O merge_copy(I0 f_i0, I0 l_i0, I1 f_i1, I1 l_i1, O f_o, R r)
{
    // Precondition: in addition to that for $\func{combine\_copy}$:
    // \hspace*{1em} $\property{weak\_ordering}(r) \wedge {}$
    // \hspace*{1em} $\func{increasing\_range}(f_{i_0}, l_{i_0}, r) \wedge
    //                \property{increasing\_range}(f_{i_1}, l_{i_1}, r)$
    relation_source<I1, I0, R> rs(r);
    return combine_copy(f_i0, l_i0, f_i1, l_i1, f_o, rs);
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        Writable(O) && Iterator(O) &&
        Relation(R) &&
        ValueType(I0) == ValueType(O) &&
        ValueType(I1) == ValueType(O) &&
        ValueType(I0) == Domain(R))
triple<I0, I1, O> merge_copy_n(I0 f_i0, DistanceType(I0) n_i0,
                               I1 f_i1, DistanceType(I1) n_i1,
                               O o, R r)
{
    // Precondition: see $\func{merge\_copy}$
    relation_source<I1, I0, R> rs(r);
    return combine_copy_n(f_i0, n_i0, f_i1, n_i1, o, rs);
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && BidirectionalIterator(I0) &&
        Readable(I1) && BidirectionalIterator(I1) &&
        Writable(O) && BidirectionalIterator(O) &&
        Relation(R) &&
        ValueType(I0) == ValueType(O) &&
        ValueType(I1) == ValueType(O) &&
        ValueType(I0) == Domain(R))
O merge_copy_backward(I0 f_i0, I0 l_i0, I1 f_i1, I1 l_i1, O l_o,
                      R r)
{
    // Precondition: in addition to that for $\func{combine\_copy\_backward}$:
    //               $\property{weak\_ordering}(r) \wedge {}$
    //               $\func{increasing\_range}(f_{i_0}, l_{i_0}, r) \wedge
    //                \property{increasing\_range}(f_{i_1}, l_{i_1}, r)$
    relation_source<I1, I0, R> rs(r);
    return combine_copy_backward(f_i0, l_i0, f_i1, l_i1, l_o,
                                 rs);
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && BidirectionalIterator(I0) &&
        Readable(I1) && BidirectionalIterator(I1) &&
        Writable(O) && BidirectionalIterator(O) &&
        Relation(R) &&
        ValueType(I0) == ValueType(O) && ValueType(I1) == ValueType(O) &&
        ValueType(I0) == Domain(R))
triple<I0, I1, O> merge_copy_backward_n(I0 l_i0, DistanceType(I0) n_i0,
                           I1 l_i1, DistanceType(I1) n_i1, O l_o, R r) {
    // Precondition: see $\func{merge\_copy\_backward}$
    relation_source<I1, I0, R> rs(r);
    return combine_copy_backward_n(l_i0, n_i0, l_i1, n_i1, l_o, rs);
}

template<typename I0, typename I1>
    requires(Mutable(I0) && Mutable(I1) &&
        ValueType(I0) == ValueType(I1))
void exchange_values(I0 x, I1 y)
{
    // Precondition: $\func{deref}(x)$ and $\func{deref}(y)$ are defined
    ValueType(I0) t = source(x);
            sink(x) = source(y);
            sink(y) = t;
}

template<typename I0, typename I1>
    requires(Mutable(I0) && ForwardIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1))
void swap_step(I0& f0, I1& f1)
{
    // Precondition: $\func{deref}(f_0)$ and $\func{deref}(f_1)$ are defined
    exchange_values(f0, f1);
    f0 = successor(f0);
    f1 = successor(f1);
}

template<typename I0, typename I1>
    requires(Mutable(I0) && ForwardIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1))
I1 swap_ranges(I0 f0, I0 l0, I1 f1)
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, l_0-f_0)$
    while (f0 != l0) swap_step(f0, f1);
    return f1;
}

template<typename I0, typename I1>
    requires(Mutable(I0) && ForwardIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1))
pair<I0, I1> swap_ranges_bounded(I0 f0, I0 l0, I1 f1, I1 l1)
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition: $\property{mutable\_bounded\_range}(f_1, l_1)$
    while (f0 != l0 && f1 != l1) swap_step(f0, f1);
    return pair<I0, I1>(f0, f1);
}

template<typename I0, typename I1, typename N>
    requires(Mutable(I0) && ForwardIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1) &&
        Integer(N))
pair<I0, I1> swap_ranges_n(I0 f0, I1 f1, N n)
{
    // Precondition: $\property{mutable\_counted\_range}(f_0, n)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, n)$
    while (count_down(n)) swap_step(f0, f1);
    return pair<I0, I1>(f0, f1);
}

template<typename I0, typename I1>
    requires(Mutable(I0) && BidirectionalIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1))
void reverse_swap_step(I0& l0, I1& f1)
{
    // Precondition: $\func{deref}(\func{predecessor}(l_0))$ and
    //               $\func{deref}(f_1)$ are defined
    l0 = predecessor(l0);
    exchange_values(l0, f1);
    f1 = successor(f1);
}

template<typename I0, typename I1>
    requires(Mutable(I0) && BidirectionalIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1))
I1 reverse_swap_ranges(I0 f0, I0 l0, I1 f1)
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, l_0-f_0)$
    while (f0 != l0) reverse_swap_step(l0, f1);
    return f1;
}

template<typename I0, typename I1>
    requires(Mutable(I0) && BidirectionalIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1))
pair<I0, I1>reverse_swap_ranges_bounded(I0 f0, I0 l0,
                                        I1 f1, I1 l1)
{
    // Precondition: $\property{mutable\_bounded\_range}(f_0, l_0)$
    // Precondition:  $\property{mutable\_bounded\_range}(f_1, l_1)$
    while (f0 != l0 && f1 != l1)
        reverse_swap_step(l0, f1);
    return pair<I0, I1>(l0, f1);
}

template<typename I0, typename I1, typename N>
    requires(Mutable(I0) && BidirectionalIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1) &&
        Integer(N))
pair<I0, I1> reverse_swap_ranges_n(I0 l0, I1 f1, N n)
{
    // Precondition: $\property{mutable\_counted\_range}(l_0-n, n)$
    // Precondition: $\property{mutable\_counted\_range}(f_1, n)$
    while (count_down(n)) reverse_swap_step(l0, f1);
    return pair<I0, I1>(l0, f1);
}


//
//  Chapter 10. Rearrangements
//


template<typename I, typename F>
    requires(Mutable(I) && Transformation(F) && I == Domain(F))
void cycle_to(I i, F f)
{
    // Precondition: The orbit of $i$ under $f$ is circular
    // Precondition: $(\forall n \in \mathbb{N})\,\func{deref}(f^n(i))$ is defined
    I k = f(i);
    while (k != i) {
        exchange_values(i, k);
        k = f(k);
    }
}

// Exercise 10.3: cycle_to variant doing 2n-1 assignments


template<typename I, typename F>
    requires(Mutable(I) && Transformation(F) && I == Domain(F))
void cycle_from(I i, F f)
{
    // Precondition: The orbit of $i$ under $f$ is circular
    // Precondition: $(\forall n \in \mathbb{N})\,\func{deref}(f^n(i))$ is defined
    ValueType(I) tmp = source(i);
    I j = i;
    I k = f(i);
    while (k != i) {
        sink(j) = source(k);
        j = k;
        k = f(k);
    }
    sink(j) = tmp;
}


// Exercise 10.4: arbitrary rearrangement using array of n boolean values
// Exercise 10.5: arbitrary rearrangement using total ordering on iterators


template<typename I>
    requires(Mutable(I) && IndexedIterator(I))
void reverse_n_indexed(I f, DistanceType(I) n)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    DistanceType(I) i(0);
    n = predecessor(n);
    while (i < n) {
        // $n = (n_\text{original} - 1) - i$
        exchange_values(f + i, f + n);
        i = successor(i);
        n = predecessor(n);
    }
}

template<typename I>
    requires(Mutable(I) && BidirectionalIterator(I))
void reverse_bidirectional(I f, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    while (true) {
        if (f == l) return;
        l = predecessor(l);
        if (f == l) return;
        exchange_values(f, l);
        f = successor(f);
    }
}

template<typename I>
    requires(Mutable(I) && BidirectionalIterator(I))
void reverse_n_bidirectional(I f, I l, DistanceType(I) n)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge 0 \leq n \leq l - f$
    reverse_swap_ranges_n(l, f, half_nonnegative(n));
}

template<typename I, typename B>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        ValueType(I) == ValueType(B))
I reverse_n_with_buffer(I f_i, DistanceType(I) n, B f_b)
{
    // Precondition: $\property{mutable\_counted\_range}(f_i, n)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n)$
    return reverse_copy(f_b, copy_n(f_i, n, f_b).m1, f_i);
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I reverse_n_forward(I f, DistanceType(I) n)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    typedef DistanceType(I) N;
    if (n < N(2)) return f + n;
    N h = half_nonnegative(n);
    N n_mod_2 = n - twice(h);
    I m = reverse_n_forward(f, h) + n_mod_2;
    I l = reverse_n_forward(m, h);
    swap_ranges_n(f, m, h);
    return l;
}

template<typename I, typename B>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        ValueType(I) == ValueType(B))
I reverse_n_adaptive(I f_i, DistanceType(I) n_i,
                     B f_b, DistanceType(I) n_b)
{
    // Precondition: $\property{mutable\_counted\_range}(f_i, n_i)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_b)$
    typedef DistanceType(I) N;
    if (n_i < N(2))
        return f_i + n_i;
    if (n_i <= n_b)
        return reverse_n_with_buffer(f_i, n_i, f_b);
    N h_i = half_nonnegative(n_i);
    N n_mod_2 = n_i - twice(h_i);
    I m_i = reverse_n_adaptive(f_i, h_i, f_b, n_b) + n_mod_2;
    I l_i = reverse_n_adaptive(m_i, h_i, f_b, n_b);
    swap_ranges_n(f_i, m_i, h_i);
    return l_i;
}

template<typename I>
    requires(RandomAccessIterator(I))
struct k_rotate_from_permutation_random_access
{
    DistanceType(I) k;
    DistanceType(I) n_minus_k;
    I m_prime;
    k_rotate_from_permutation_random_access(I f, I m, I l) :
        k(l - m), n_minus_k(m - f), m_prime(f + (l - m))
    {
        // Precondition: $\property{bounded\_range}(f, l) \wedge m \in [f, l)$
    }
    I operator()(I x)
    {
        // Precondition: $x \in [f, l)$
        if (x < m_prime) return x + n_minus_k;
        else             return x - k;
    }
};

template<typename I>
    requires(IndexedIterator(I))
struct k_rotate_from_permutation_indexed
{
    DistanceType(I) k;
    DistanceType(I) n_minus_k;
    I f;
    k_rotate_from_permutation_indexed(I f, I m, I l) :
        k(l - m), n_minus_k(m - f), f(f)
    {
        // Precondition: $\property{bounded\_range}(f, l) \wedge m \in [f, l)$
    }
    I operator()(I x)
    {
        // Precondition: $x \in [f, l)$
        DistanceType(I) i = x - f;
        if (i < k) return x + n_minus_k;
        else       return f + (i - k);
    }
};

template<typename I, typename F>
    requires(Mutable(I) && IndexedIterator(I) &&
        Transformation(F) && I == Domain(F))
I rotate_cycles(I f, I m, I l, F from)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge m \in [f, l]$
    // Precondition: $from$ is a from-permutation on $[f, l)$
    typedef DistanceType(I) N;
    N d = gcd<N, N>(m - f, l - m);
    while (count_down(d)) cycle_from(f + d, from);
    return f + (l - m);
}

template<typename I>
    requires(Mutable(I) && IndexedIterator(I))
I rotate_indexed_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    k_rotate_from_permutation_indexed<I> p(f, m, l);
    return rotate_cycles(f, m, l, p);
}

template<typename I>
    requires(Mutable(I) && RandomAccessIterator(I))
I rotate_random_access_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    k_rotate_from_permutation_random_access<I> p(f, m, l);
    return rotate_cycles(f, m, l, p);
}


template<typename I>
    requires(Mutable(I) && BidirectionalIterator(I))
I rotate_bidirectional_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    reverse_bidirectional(f, m);
    reverse_bidirectional(m, l);
    pair<I, I> p = reverse_swap_ranges_bounded(m, l, f, m);
    reverse_bidirectional(p.m1, p.m0);
    if (m == p.m0) return p.m1;
    else           return p.m0;
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
void rotate_forward_annotated(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
                                      DistanceType(I) a = m - f;
                                      DistanceType(I) b = l - m;
    while (true) {
        pair<I, I> p = swap_ranges_bounded(f, m, m, l);
        if (p.m0 == m && p.m1 == l) { Assert(a == b);
            return;
        }
        f = p.m0;
        if (f == m) {                 Assert(b > a);
            m = p.m1;                 b = b - a;
        } else {                      Assert(a > b);
                                      a = a - b;
        }
    }
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
void rotate_forward_step(I& f, I& m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    I c = m;
    do {
        swap_step(f, c);
        if (f == m) m = c;
    } while (c != l);
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I rotate_forward_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    rotate_forward_step(f, m, l);
    I m_prime = f;
    while (m != l) rotate_forward_step(f, m, l);
    return m_prime;
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I rotate_partial_nontrivial(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return swap_ranges(m, l, f);
}

// swap_ranges_backward
// rotate_partial_backward_nontrivial

template<typename I, typename B>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B))
I rotate_with_buffer_nontrivial(I f, I m, I l, B f_b)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    // Precondition: $\property{mutable\_counted\_range}(f_b, l-f)$
    B l_b = copy(f, m, f_b);
    I m_prime = copy(m, l, f);
    copy(f_b, l_b, m_prime);
    return m_prime;
}

template<typename I, typename B>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        Mutable(B) && ForwardIterator(B))
I rotate_with_buffer_backward_nontrivial(I f, I m, I l, B f_b)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    // Precondition: $\property{mutable\_counted\_range}(f_b, l-f)$
    B l_b = copy(m, l, f_b);
    copy_backward(f, m, l);
    return copy(f_b, l_b, f);
}


// Section 10.5. Algorithm selection


template<typename I>
    requires(Mutable(I) && IndexedIterator(I))
void reverse_indexed(I f, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    reverse_n_indexed(f, l - f);
}


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

// NeedsConstruction and NeedsDestruction should be overloaded for every POD type

template<typename T>
    requires(Regular(T))
struct temporary_buffer
{
    typedef pointer(T) P;
    typedef DistanceType(P) N;
    P p;
    N n;
    temporary_buffer(N n_) : n(n_)
    {
        while (true) {
            p = P(malloc(n * sizeof(T)));
            if (p != P(0)) {
                construct_all(p, p + n);
                return;
            }
            n = half_nonnegative(n);
        }
    }
    ~temporary_buffer()
    {
        destroy_all(p, p + n);
        free(p);
    }
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

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
void reverse_n_with_temporary_buffer(I f, DistanceType(I) n)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    temporary_buffer<ValueType(I)> b(n);
    reverse_n_adaptive(f, n, begin(b), size(b));
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I rotate(I f, I m, I l)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge m \in [f, l]$
    if (m == f) return l;
    if (m == l) return f;
    return rotate_nontrivial(f, m, l, IteratorConcept(I)());
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I rotate_nontrivial(I f, I m, I l, forward_iterator_tag)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return rotate_forward_nontrivial(f, m, l);
}

template<typename I>
    requires(Mutable(I) && BidirectionalIterator(I))
I rotate_nontrivial(I f, I m, I l, bidirectional_iterator_tag)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return rotate_bidirectional_nontrivial(f, m, l);
}

template<typename I>
    requires(Mutable(I) && IndexedIterator(I))
I rotate_nontrivial(I f, I m, I l, indexed_iterator_tag)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return rotate_indexed_nontrivial(f, m, l);
}

template<typename I>
    requires(Mutable(I) && RandomAccessIterator(I))
I rotate_nontrivial(I f, I m, I l, random_access_iterator_tag)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l) \wedge f \prec m \prec l$
    return rotate_random_access_nontrivial(f, m, l);
}


//
//  Chapter 11. Partition and merging
//


// Exercise 11.1:

template<typename I,  typename P>
    requires(Readable(I) && Iterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
bool partitioned_at_point(I f, I m, I l, P p)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l) \wedge m \in [f, l]$
    return none(f, m, p) && all(m, l, p);
}


// Exercise 11.2:

template<typename I, typename P>
    requires(Readable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I potential_partition_point(I f, I l, P p)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l)$
    return count_if_not(f, l, p, f);
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I partition_semistable(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    I i = find_if(f, l, p);
    if (i == l) return i;
    I j = successor(i);
    while (true) {
        j = find_if_not(j, l, p);
        if (j == l) return i;
        swap_step(i, j);
    }
}

// Exercise 11.3: rewrite partition_semistable, expanding find_if_not inline and
// eliminating extra test against l


// Exercise 11.4: substitute copy_step(j, i) for swap_step(i, j) in partition_semistable

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I remove_if(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    I i = find_if(f, l, p);
    if (i == l) return i;
    I j = successor(i);
    while (true) {
        j = find_if_not(j, l, p);
        if (j == l) return i;
        copy_step(j, i);
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

template<typename I, typename P>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I partition_bidirectional(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    while (true) {
        f = find_if(f, l, p);
        l = find_backward_if_not(f, l, p);
        if (f == l) return f;
        reverse_swap_step(l, f);
    }
}

// Exercise 11.6:

template<typename I,  typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I partition_forward(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    I i = count_if_not(f, l, p, f);
    I j = i;
    while (true) {
        j = find_if_not(j, l, p);
        if (j == l) return i;
        f = find_if_unguarded(f, p);
        swap_step(f, j);
    }
}

// Exercise 11.7: partition_single_cycle

template<typename I, typename P>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I partition_single_cycle(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    f = find_if(f, l, p);
    l = find_backward_if_not(f, l, p);
    if (f == l) return f;
    l = predecessor(l);
    ValueType(I) tmp = source(f);
    while (true) {
        sink(f) = source(l);
        f = find_if(successor(f), l, p);
        if (f == l) {
            sink(l) = tmp;
            return f;
        }
        sink(l) = source(f);
        l = find_backward_if_not_unguarded(l, p);
    }
}


// Exercise 11.8: partition_sentinel

template<typename I, typename P>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I partition_bidirectional_unguarded(I f, I l, P p)
{
    // Precondition:
    // $(\neg \func{all}(f, l, p) \wedge \func{some}(f, l, p)) \vee
    // (\neg p(\func{source}(f-1)) \wedge p(\func{source}(l)))$
    while (true) {
        f = find_if_unguarded(f, p);
        l = find_backward_if_not_unguarded(l, p);
        if (successor(l) == f) return f;
        exchange_values(f, l);
        f = successor(f); // $\neg p(\func{source}(f-1)) \wedge p(\func{source}(l))$
    }
}

template<typename I, typename P>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I partition_sentinel(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    f = find_if(f, l, p);
    l = find_backward_if_not(f, l, p);
    if (f == l) return f;
    l = predecessor(l);
    exchange_values(f, l);
    f = successor(f);
    return partition_bidirectional_unguarded(f, l, p);
}


// Exercise 11.9: partition_single_cycle_sentinel


template<typename I, typename P>
    requires(Mutable(I) && IndexedIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I partition_indexed(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    typedef DistanceType(I) N;
    N i(0);
    N j = l - f;
    while (true) {
        while (true) {
            if (i == j) return f + i;
            if (p(source(f + i))) break;
            i = successor(i);
        }
        while (true) {
            j = predecessor(j);
            if (i == j) return f + j + 1;
            if (!p(source(f + j))) break;
        }
        exchange_values(f + i, f + j);
        i = successor(i);
    }
}

template<typename I, typename B, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        ValueType(I) == ValueType(B) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I partition_stable_with_buffer(I f, I l, B f_b, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, l-f)$
    pair<I, B> x = partition_copy(f, l, f, f_b, p);
    copy(f_b, x.m1, x.m0);
    return x.m0;
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, I> partition_stable_singleton(I f, P p)
{
    // Precondition: $\property{readable\_bounded\_range}(f, \func{successor}(f))$
    I l = successor(f);
    if (!p(source(f))) f = l;
    return pair<I, I>(f, l);
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
pair<I, I> combine_ranges(const pair<I, I>& x,
                          const pair<I, I>& y)
{
    // Precondition: $\property{mutable\_bounded\_range}(x.m0, y.m0)$
    // Precondition: $x.m1 \in [x.m0, y.m0]$
    return pair<I, I>(rotate(x.m0, x.m1, y.m0), y.m1);
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, I> partition_stable_n_nonempty(I f, DistanceType(I) n,
                                       P p)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n) \wedge n > 0$
    if (one(n)) return partition_stable_singleton(f, p);
    DistanceType(I) h = half_nonnegative(n);
    pair<I, I> x = partition_stable_n_nonempty(f, h, p);
    pair<I, I> y = partition_stable_n_nonempty(x.m1, n - h, p);
    return combine_ranges(x, y);
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, I> partition_stable_n(I f, DistanceType(I) n, P p)
{
    // Precondition: $\property{mutable\_counted\_range}(f, n)$
    if (zero(n)) return pair<I, I>(f, f);
    return partition_stable_n_nonempty(f, n, p);
}


// Exercise 11.10: partition_stable_n_adaptive


template<typename I, typename P>
   requires(Mutable(I) && ForwardIterator(I) &&
       UnaryPredicate(P) && Domain(P) == ValueType(I)\)
I partition_stable(I f, I l, P p)
{
    // Precondition: $\property{mutable\_bounded\_range}(f, l)$
    return partition_stable_n(f, l - f, p).m0;
}

template<typename I, typename P>
    requires(ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
struct partition_trivial
{
    P p;
    partition_trivial(const P & p) : p(p) {}
    pair<I, I> operator()(I i)
    {
        return partition_stable_singleton<I, P>(i, p);
    }
};

template<typename I, typename P>
    requires(ForwardIterator(I) && UnaryPredicate(P) && ValueType(I) == Domain(P))
struct codomain_type< partition_trivial<I, P> >
{
    typedef pair<I, I> type;
};

template<typename I, typename Op>
    requires(Mutable(I) && ForwardIterator(I) &&
        BinaryOperation(Op) && ValueType(I) == Domain(Op))
Domain(Op) add_to_counter(I f, I l, Op op, Domain(Op) x,
                          const Domain(Op)& z)
{
    if (x == z) return z;
    while (f != l) {
        if (source(f) == z) {
            sink(f) = x;
            return z;
        }
        x = op(source(f), x);
        sink(f) = z;
        f = successor(f);
    }
    return x;
}

template<typename Op>
    requires(BinaryOperation(Op))
struct counter_machine
{
    typedef Domain(Op) T;
    Op op;
    T z;
    T f[64];
    DistanceType(pointer(T)) n;
    counter_machine(Op op, const Domain(Op)& z) :
    op(op), z(z), n(0) { }
    void operator()(const T& x)
    {
        // Precondition: must not be called more than $2^{64}-1$ times
         T tmp = add_to_counter(f, f + n, op, x, z);
         if (tmp != z) {
             sink(f + n) = tmp;
             n = successor(n);
         }
    }
};

template<typename Op>
    requires(BinaryOperation(Op))
struct transpose_operation
{
    Op op;
    transpose_operation(Op op) : op(op) { }
    typedef Domain(Op) T;
    T operator()(const T& x, const T& y)
    {
        return op(y, x);
    }
};

template<typename Op>
    requires(BinaryOperation(Op))
struct input_type< transpose_operation<Op>, 0 >
{
    typedef Domain(Op) type;
};

template<typename I, typename Op, typename F>
    requires(Iterator(I) && BinaryOperation(Op) &&
        UnaryFunction(F) && I == Domain(F) &&
        Codomain(F) == Domain(Op))
Domain(Op) reduce_balanced(I f, I l, Op op, F fun,
                           const Domain(Op)& z)
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge l - f < 2^{64}$
    // Precondition: $\property{partially\_associative}(op)$
    // Precondition: $(\forall x \in [f, l))\,fun(x)$ is defined
    counter_machine<Op> c(op, z);
    while (f != l) {
        c(fun(f));
        f = successor(f);
    }
    transpose_operation<Op> t_op(op);
    return reduce_nonzeroes(c.f, c.f + c.n, t_op, z);
}

template<typename I, typename Op>
    requires(ReadableIterator(I) && BinaryOperation(Op) &&
        ValueType(I) == Domain(Op))
Domain(Op) reduce_balanced(I f, I l, Op op, const Domain(Op)& z)
{
    // Precondition: $\property{readable\_bounded\_range}(f, l) \wedge l-f < 2^{33}$
    // Precondition: $\property{partially\_associative}(op)$
    counter_machine<Op> c(op, z);
    while (f != l) {
        c(source(f));
        f = successor(f);
    }
    transpose_operation<Op> t_op(op);
    return reduce_nonzeroes(c.f, c.f + c.n, t_op, z);
}


template<typename I, typename P>
    requires(ForwardIterator(I) && UnaryPredicate(P) &&
        ValueType(I) == Domain(P))
I partition_stable_iterative(I f, I l, P p)
{
    // Precondition: $\property{bounded\_range}(f, l) \wedge l - f < 2^{64}$
    return reduce_balanced(
        f, l,
        combine_ranges<I>,
        partition_trivial<I, P>(p),
        pair<I, I>(f, f)
      ).m0;
}

template<typename I, typename B, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        ValueType(I) == ValueType(B) &&
        Relation(R) && ValueType(I) == Domain(R))
I merge_n_with_buffer(I f0, DistanceType(I) n0,
                      I f1, DistanceType(I) n1, B f_b, R r)
{
    // Precondition: $\func{mergeable}(f_0, n_0, f_1, n_1, r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_0)$
    copy_n(f0, n0, f_b);
    return merge_copy_n(f_b, n0, f1, n1, f0, r).m2;
}

template<typename I, typename B, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        ValueType(I) == ValueType(B) &&
        Relation(R) && ValueType(I) == Domain(R))
I sort_n_with_buffer(I f, DistanceType(I) n, B f_b, R r)
{
    // Property:
    // $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, \lceil n/2 \rceil)$
    DistanceType(I) h = half_nonnegative(n);
    if (zero(h)) return f + n;
    I m = sort_n_with_buffer(f, h,     f_b, r);
          sort_n_with_buffer(m, n - h, f_b, r);
    return merge_n_with_buffer(f, h, m, n - h, f_b, r);
}

template<typename I, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Relation(R) && ValueType(I) == Domain(R))
void merge_n_step_0(I f0, DistanceType(I) n0,
                    I f1, DistanceType(I) n1, R r,
                    I& f0_0, DistanceType(I)& n0_0,
                    I& f0_1, DistanceType(I)& n0_1,
                    I& f1_0, DistanceType(I)& n1_0,
                    I& f1_1, DistanceType(I)& n1_1)
{
    // Precondition: $\property{mergeable}(f_0, n_0, f_1, n_1, r)$
    f0_0 = f0;
    n0_0 = half_nonnegative(n0);
    f0_1 = f0_0 + n0_0;
    f1_1 = lower_bound_n(f1, n1, source(f0_1), r);
    f1_0 = rotate(f0_1, f1, f1_1);
    n0_1 = f1_0 - f0_1;
    f1_0 = successor(f1_0);
    n1_0 = predecessor(n0 - n0_0);
    n1_1 = n1 - n0_1;
}

template<typename I, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Relation(R) && ValueType(I) == Domain(R))
void merge_n_step_1(I f0, DistanceType(I) n0,
                    I f1, DistanceType(I) n1, R r,
                    I& f0_0, DistanceType(I)& n0_0,
                    I& f0_1, DistanceType(I)& n0_1,
                    I& f1_0, DistanceType(I)& n1_0,
                    I& f1_1, DistanceType(I)& n1_1)
{
    // Precondition: $\property{mergeable}(f_0, n_0, f_1, n_1, r)$
    f0_0 = f0;
    n0_1 = half_nonnegative(n1);
    f1_1 = f1 + n0_1;
    f0_1 = upper_bound_n(f0, n0, source(f1_1), r);
    f1_1 = successor(f1_1);
    f1_0 = rotate(f0_1, f1, f1_1);
    n0_0 = f0_1 - f0_0;
    n1_0 = n0 - n0_0;
    n1_1 = predecessor(n1 - n0_1);
}

template<typename I, typename B, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        ValueType(I) == ValueType(B) &&
        Relation(R) && ValueType(I) == Domain(R))
I merge_n_adaptive(I f0, DistanceType(I) n0,
                   I f1, DistanceType(I) n1,
                   B f_b, DistanceType(B) n_b, R r)
{
    // Precondition: $\property{mergeable}(f_0, n_0, f_1, n_1, r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_b)$
    typedef DistanceType(I) N;
    if (zero(n0) || zero(n1)) return f0 + n0 + n1;
    if (n0 <= N(n_b))
        return merge_n_with_buffer(f0, n0, f1, n1, f_b, r);
    I f0_0; I f0_1; I f1_0; I f1_1;
    N n0_0; N n0_1; N n1_0; N n1_1;
    if (n0 < n1) merge_n_step_0(
                            f0, n0, f1, n1, r,
                            f0_0, n0_0, f0_1, n0_1,
                            f1_0, n1_0, f1_1, n1_1);
    else         merge_n_step_1(
                            f0, n0, f1, n1, r,
                            f0_0, n0_0, f0_1, n0_1,
                            f1_0, n1_0, f1_1, n1_1);
           merge_n_adaptive(f0_0, n0_0, f0_1, n0_1,
                            f_b, n_b, r);
    return merge_n_adaptive(f1_0, n1_0, f1_1, n1_1,
                            f_b, n_b, r);
}

template<typename I, typename B, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        ValueType(I) == ValueType(B) &&
        Relation(R) && ValueType(I) == Domain(R))
I sort_n_adaptive(I f, DistanceType(I) n,
                  B f_b, DistanceType(B) n_b, R r)
{
    // Precondition:
    // $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    // Precondition: $\property{mutable\_counted\_range}(f_b, n_b)$
    DistanceType(I) h = half_nonnegative(n);
    if (zero(h)) return f + n;
    I m = sort_n_adaptive(f, h,     f_b, n_b, r);
          sort_n_adaptive(m, n - h, f_b, n_b, r);
    return merge_n_adaptive(f, h, m, n - h, f_b, n_b, r);
}

template<typename I, typename R>
    requires(Mutable(I) && ForwardIterator(I) &&
        Relation(R) && ValueType(I) == Domain(R))
I sort_n(I f, DistanceType(I) n, R r)
{
    // Precondition:
    // $\property{mutable\_counted\_range}(f, n) \wedge \property{weak\_ordering}(r)$
    temporary_buffer<ValueType(I)> b(half_nonnegative(n));
    return sort_n_adaptive(f, n, begin(b), size(b), r);
}


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
