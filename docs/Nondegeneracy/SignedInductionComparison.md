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
