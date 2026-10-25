# The mixed quadratic test for signed induction

Status: the signed right-multiplier identities and the nonzero matrix test below
are checked in `QuiverHecke/CyclotomicAction/SignedMultipliers.lean`. The
comparison with the whole upward presentation, including braids, remains open.
This is not a counterexample to existence of the cyclotomic action.

## Conventions and necessary correction

Let σ be the parity involution of a superalgebra. For odd u write
`R_u(h)=σ(h)u`. Ordinary operator composition gives

`R_u R_v(h) = -hvu` for odd v.

Thus putting a minus on **both** directed odd crossings does not remove the
mixed quadratic sign. If the original double crossing is the constant 1,
the resulting double operator is minus the identity. The same failure occurs
with neither crossing negated. Rank-one normalization by itself is not a
multicolour prescription.

`oddRight_comp` and `neg_oddRight_comp` prove these identities over any ring
with a specified involutive ring endomorphism. `asymmetric_oddRight_comp`
checks the local repair obtained by negating only one multiplier. This local
repair does not establish compatibility with all triples or with strand
inclusions.

## Exact nonzero two-word instance

Use `M₂(ℚ)` with parity involution `h ↦ PhP`, where

```
P = diag(1,-1),   u = [[0,1],[1,0]].
```

The diagonal matrix units are the word idempotents ij and ji; the off-diagonal
matrix units are odd directed crossings. Set the dots to zero. This is the
quadratic block for two distinct disconnected odd colours with constant
parameter 1 and cutoff one. In particular, `u²=1` and `σ(u)=-u`.

The regular-module calculation at h=1 gives

`(-R_u)(-R_u)(1) = -1 ≠ 1`.

The declaration `uniform_crossing_sign_fails` checks this on the matrix
carrier, not by assuming a nonzero identity. `directed_crossing_sign_passes`
checks the opposite-sign local composition. The identification with the
presented two-colour cyclotomic quotient is explanatory here, not a Lean
quotient isomorphism; the formal result is the exact regular-matrix instance.

## A connected asymmetric polynomial test

`CyclotomicAction.AsymmetricParameters` constructs a compatible all-odd
Cartan datum with matrix `[[2,-2],[-4,2]]`, positive symmetrizer `(2,1)`,
and homogeneous rational parameters with `Q(u,v)=u²+v⁴`. It verifies the
literal `SKM.SerrePolynomial.quadraticValue` formula.

Odd signed right multiplication squares to negative right multiplication by
the dot square, whereas its fourth power has positive sign. Consequently,
with the dots fixed to these operators, the two terms of this Q acquire
opposite signs. In square coordinates the exact obstruction is

`¬ ∃ c ∈ ℚ, ∀ z,w ∈ ℚ, c(z+w²) = -z+w²`.

`no_common_quadratic_scalar` proves this using `(z,w)=(1,0),(0,1)`.
Thus even allowing the product of directed crossing scalars to vary does
not generally repair **unchanged parameters**. Individual dot signs do not
alter even powers either. This strengthens the constant-square test; it
still does not exclude word reversal or transported parameters.

The same module constructs valid homogeneous `transportedScalars` with
`Q'(u,v)=u²-v⁴`, and `transported_mixed_square` proves the signed operator
quadratic comparison from that source relation. This is a relation-transfer
theorem with the source multiplication relation as a hypothesis, not yet a
homomorphism from the specified presentation or a functor on projectives.
The corresponding braid and adjunction comparison must still be assembled.

## Remaining acceptance boundary

A complete comparison must specify directed crossing scalars and the algebra
parameters simultaneously. Alternatively it may transport to a changed
parameter family and prove that this is the family used for induction. A
uniform sign with unchanged parameters is already excluded by the instance
above. The signed Chevalley symmetry is not refuted: it also changes the
orientation and source presentation, which this naive assignment does not.

Still required are the complete mixed square polynomial, the repeated-outer-
colour braid correction, and compatibility with the prescribed dots and
adjunction. No claim of node A0 follows from these local identities.
