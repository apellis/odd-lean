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

This is **not yet** a unique right-PBW expansion with old quotient Hom
coefficients. The raw index `PrependIdx` still contains the old PBW index;
its expansion therefore has nonzero kernel whenever old cyclotomic
relations exist. Treating this surjection as injective would be incorrect.

The remaining indispensable step is to regroup these raw indices by
moving exponent, inverse shuffle, and old target, prove the inverse with
`Old(v,t)` coefficients, and identify the old relation span coordinatewise.
That requires compatibility of extraction with arbitrary old composition,
not only the individual old normal forms handled here. The checked scalar
`prependCoefficients_right` supplies the affine matrix analogue, but does
not by itself supply the full super coefficient/old-ideal comparison.
After that inverse is constructed, the moving square must be identified
with the exponent shift by two (and the even moving dot with shift by one),
and the finite-support leading-coordinate argument can prove the requested
difference injectivity. No such injectivity is asserted by this module.

The concrete consumer uses one old odd strand, one new odd dot, cutoff
three, and the inhomogeneous coefficient `1 + delta`; it also checks that
the moving tail has odd parity. The headline axiom checks use only
`propext`, `Classical.choice`, and `Quot.sound`.
