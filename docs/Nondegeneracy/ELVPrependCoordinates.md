# Full ELV coefficients in input-side PBW coordinates

## Statement and provenance

`ELVPrependCoordinates.lean` proves the coefficient-normalization comparison
needed before the cancellation argument of `DeformedGlobalQP.md` §1.
The scalar input PBW basis is `prependBasis`, already used by
`PrependCoefficientCoordinates.lean` and `PrependTensorCoordinates.lean`.
No second permutation or normal-form indexing system is introduced.

KKO I, arXiv:1206.5933v2, p. 38, equations (8.1)–(8.2), fixes the right
old-algebra and parity-shift conventions. Lemma 8.1 on p. 39 states right
projectivity and monic skew-polynomial injectivity. The full ELV exterior
coefficient extension below is a separate comparison; it is not claimed
to be a statement of that lemma.

Write `A` for the full `ELVCoefficientAlgebra D cutoff`. For words `v,w`,
`prependAffineEquiv` is an actual linear equivalence

```
Hom_ELV(i :: v, w) ≃ₗ[k] (PrependIdx i v w →₀ A).
```

It is the tensor extension of the existing scalar `prependBasis.repr`.
Its inverse takes `single x a` to `a ⊗ prependElt x`. This neither assumes
flatness nor forms a quotient by a polynomial on the moving strand.

## First-position coefficients and the old block

For an existing input PBW index `x`, let `b = x.old.nf` and let `T_x` be
the new dots followed by the inverse-shuffle crossing. The proved identity
`prependElt_insert_tail` is

```
prependElt x = (i ◁ b) ≫ T_x.
```

Let `r_x` be the parity of `T_x`, computed from its positioned generators,
and write `c_r` for the parity involution on `A`. Then
`prepend_insert_twisted_coefficient` proves, for **every** coefficient `a`,
including inhomogeneous ones,

```
insert (c_(r_x)(a) ⊗ b) ≫ (1 ⊗ T_x) = a ⊗ prependElt x.
```

The coefficient stays in the first tensor position. The multiplication
in `SuperalgebraCat` has the categorical/opposite orientation used by
`ELVOld`; the proof uses `BoxProd.tmulHom_comp_tmulHom`, not an unsigned
tensor multiplication formula.

If `p` is the balance parity, the old coefficient of this term is

```
[twist_p (c_(r_x)(a) ⊗ b)] ∈ Old(v, x.oldTarget).
```

Here `twist_p` acts on **total** parity of the coefficient and old diagram,
whereas `c_(r_x)` acts only on coefficient parity. These are distinct
operations. `prependBalancedTerm` pairs this old class with `1 ⊗ T_x`
in the existing `BalancedTensor`.

## Proved comparison and residual boundary

For a finite coordinate vector `f`, `prependBalancedExpansion` sums the
normalized terms above. The headline `balancedEquiv_prependExpansion`
proves

```
balancedEquiv (prependBalancedExpansion f)
  = projection (prependAffineEquiv.symm f).
```

Thus the expansion is surjective onto the proved balanced tensor. Its
kernel is exactly the preimage of `ELVOld.relations`, the old-only relation
span (`prependBalancedExpansion_eq_zero_iff`). The old quotient is kept
as a coefficient object in every term; its flatness is never required.

The **raw-index** expansion is not injective: `PrependIdx` still contains
the old PBW index, and its kernel is the genuine preimage of the old
cyclotomic relation span described above. It must not be confused with
the following **old-Hom quotient** equivalence, which is now proved.

`ELVPrependCrossTail.lean` regroups by moving exponent and inverse shuffle
and proves extraction vanishes on every different tail. The old target is
retained through the dependent coefficient `Old(v,t)`.
`ELVPrependDescent.lean` then kills every old-relation generator with an
arbitrary continuation (`prependExtractOldQuotient_old_generator`),
descends extraction, and proves both inverse laws for

```
prependOldCoordinateEquiv :
  Target i v w ≃ₗ[k] ⨁ q : PrependIdx.Tail i v w, Old(v, q.oldTarget).
```

Thus simultaneous quotient coordinates, including arbitrary old Homs and
all exterior coefficients, are no longer a remaining obligation. Neither
this equivalence nor its proof asserts injectivity of the raw-index map.

`ELVMovingShift.lean` identifies actual precomposition by the source
moving power with shifting the existing tail exponent. Its
`movingSquare_coordinate_shift` gives shift by two; its
`movingEvenDot_coordinate_shift` gives shift by one at even moving colour.
These use the old-Hom equivalence, not an assumed shift operator. Total
balance parity and coefficient parity remain separate.

The same module proves `oldSourceTarget_pair`: actual right multiplication
by an inserted old source morphism changes only the old quotient coefficient
by precomposition with its total-parity twist. Hence `oldSourceTarget_above`
proves, rather than assumes, preservation of the moving-exponent filtration.
The maximum nonzero finite-support coordinate gives
`lastDotSquareDifference_injective` and `lastDotEvenDifference_injective`.
For a nonempty old word, `lastDotDifference_projection` identifies these
operators with actual right multiplication by `x_(n+1)^2 - x_1^2`, or by
`x_(n+1) - x_1` at even moving colour. The nonempty condition is essential
for this identification: the empty-word initial case is not a cancellation
of `x_1 - x_1`.

Remaining: the all-prefix relation-killing, QP induction, old-generator P
balance, and the resulting projective-resolution/exactness comparisons.
The cancellation theorem is an ingredient, not an all-prefix QP theorem.

The concrete consumer uses one old odd strand, one new odd dot, cutoff
three, and the inhomogeneous coefficient `1 + delta`; it also checks that
the moving tail has odd parity. The headline axiom checks use only
`propext`, `Classical.choice`, and `Quot.sound`.
