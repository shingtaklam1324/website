---
title: "Formalising polynomials"
date: 2020-08-22
---

One thing that comes up frequently in mathematics is the idea of polynomials, and we would like to be able to reason on any polynomial. To do this requires us to develop the theory of polynomials.

To start off, we need the definition of polynomials. Wikipedia says

> In mathematics, a polynomial is an expression consisting of variables (also called indeterminates) and coefficients, that involves only the operations of addition, subtraction, multiplication, and non-negative integer exponents of variables

In summary, a polynomial is a sum of monomials, terms of the form `a * x^n * y^m * ...` (a **finite** product) where `a` is a value in the ring, `x`, `y`, ... are variables and `n`, `m`, ... are natural numbers.

## Lists

To represent a polynomial, the basic represenation could be using a list to store the coefficients. For example, the polynomial `1 + 3x + 5x^2 + 7x^3` could be stored as `[1, 3, 5, 7]` and `1 + x^2 + x^3` can be `[1, 0, 1, 1]`. However this representation comes with it's own issues.

The first and foremost is that representations are not unique. If we have `1 + x^2 + x^3` from before, then `[1, 0, 1, 1]`, `[1, 0, 1, 1, 0]`, `[1, 0, 1, 1, 0, 0]` ... are all valid representations of this polynomial.

One way to solve this would be to add in a requirement for the last coefficient to be non-zero. This is what is commonly done in mathematics, however this comes with it's own issues, as adding a proof term to the definition makes it more difficult to reason with and requires additional proofs when creating definitions that generate polynomials. Also, the polynomial `0` is a valid polynomial which we would like to be able to reason with as well. We can't represent this using the singleton list `[0]`, as this would not satisfy the criteria for the last item in the list to be non-zero. The alternative would be to store it using the empty list `[]`, however reasoning about the last term of potentially empty lists brings it's own issues.

Another way to solve this is to add an equivalence relation on polynomials and consider the quotient. A similar approach is used in mathlib to represent multisets as a quotient of lists by permutations. However, this method does not generalise as well when the polynomials in question have multiple variables.

## Hash map

Another method would be to model the polynomial as a hash map where `polynomial R` is a hash map from `ℕ` to `R`. So the polynomial `1 + x^2 + x^3` could be represented by `{0: 1, 2: 1, 3: 1}` (to use Python's representation for dictionaries), and `1 + 3x + 5x ^2 + 7x^3` would be `{0: 1, 1: 3, 2: 5, 3: 7}`.

Right now, this still has the issue of zero coefficients. However, this is in fact much easier to solve, as we just need a constraint that all the values in the hash map must be non zero. This ends up being simpler to reason with when compared to the last item in the list like before, since we do not have the worry about potentially empty lists like before, and reasoning about adding two polynomials is also much simpler. Another benefit is with large polynomials. Say if we have the polynomial `1 + x^100`, then the list representing this has length `100`. Whereas with a hashmap, we only need to store two coefficients and exponents.

## Finitely Supported Functions

The two methods above for storing polynomials are quite good for computations, and the hash map is getting quite close to what we want. However, we don't necessarily want to limit ourselves to a hash map, and generalizing over the underlying data structure can be helpful, as we care about properties, not implementations. So let's analyse what we need:

* A function from `ℕ` to `R` (powers to coefficients)
  * which returns a non-zero value for finitely many inputs
  * and returns zero otherwise

One way to implement this would be:

* A function `f : ℕ → R`
* A finite set `s : finset ℕ`
* A proof that `f n ≠ 0 ↔ n ∈ s`

In fact, the properties we want here are known as a finitely supported function, and this is how mathlib implements polynomials.

```lean
structure finsupp (α : Type*) (β : Type*) [has_zero β] :=
(support            : finset α)
(to_fun             : α → β)
(mem_support_to_fun : ∀a, a ∈ support ↔ to_fun a ≠ 0)
```

and `polynomial R` is just implemented as

```lean
def polynomial (R : Type*) [semiring R] := add_monoid_algebra R ℕ
```

(`add_monoid_algebra` is just a thin wrapper type over `finsupp`, the definition above is the same as `finsupp ℕ R`).

## Extension to multi-variate polynomials

Another benefit of this approach is that it generalises very nicely to multi-variate polynomials. If we look at the polynomial `x^2 + 2xy + y^2`, then a list would not be a good approach. Even though there is a bijection between `ℕ` and `ℕ²` (and higher powers), it a very inefficient approach, as there will be a large number of `0` terms when representing more complex polynomials.

The hash map approach generalises quite well. We first need a set of variables `x_1`, `x_2`, and so on. Note that the index doesn't have to be a natural number, so we can use an arbitrary indexing type `σ`. Then we can use a hash map to represent the exponent in each term, and then use those hash maps to store the coefficients. So if we have a multivariate poylnomial with indexing type `σ` and coefficients in `R`, we can represent it with

```text
hashmap (hashmap σ ℕ) R
```

So the polynomial `p = x^2 + 2xy + y^2` could be stored like so:

Let `σ` be an inductive type with constructors `x` and `y`, then `p` can be stored as `{{x:2}:1, {x:1,y:1}:2, {y:2}:1}`.

Much like we abstracted away the implementation details for single variable polynomials, we can do the same for multi variable polynomials. In mathlib, multivariate polynomials are defined like so:

```lean
def mv_polynomial (σ : Type*) (α : Type*) [comm_semiring α] := add_monoid_algebra α (σ →₀ ℕ)
```

which is equivalent to

```lean
finsupp (finsupp σ ℕ) R
```
