# Integer support of the coefficient-weight-truncated cyclotomic Homs

## Checked theorem

`ELVOld.truncatedContent_bounded` proves, for every pair of words `v,w`, every
coefficient-weight cutoff `N`, and every finite colour datum, that there is a
natural number `B` such that

```
n < -B ∨ B < n → truncatedDegree v w n = ⊥.
```

There is no bound on word length, no restriction on repetitions or parity,
and no freeness, rank, nondegeneracy, or finite-weight-fibre hypothesis. The
coefficient algebra is the full ELV algebra, including exterior generators.
The scalar ring remains an arbitrary commutative ring.

`truncatedContent_bounded_of_bound` works for arbitrary colour sets with a
uniform bound on coefficient degree divided by total coefficient weight.
This is an arithmetic coefficient bound, not a homogeneous-support premise.

## Proof

1. The concrete monic endpoint annihilator reduces every moving-dot power to
   a bounded power with an old coefficient. The right-sided recurrence does
   not commute arbitrary coefficients past an odd dot.
2. `appendFiniteRangeSpan_eq_top` proves spanning by finitely many crossing
   skeletons and bounded moving exponents. Each range map factors through
   the smaller **coefficient-truncated** cyclotomic Hom, not just the affine
   old endomorphism ring. Parity twists are retained when moving the dot
   power to the source side.
3. `appendCrossingSkeleton_map_mem_degree` proves the concrete degree shift
   of each range map. Homogeneity uses actual dot and crossing diagrams and
   the homogeneous right-context map.
4. The vacuum Hom is spanned by coefficient identities. Coefficient basis
   elements of total weight at least `N` lie in the actual truncation ideal;
   retained elements have degrees between zero and `M*N`. A nonempty target
   with empty source has zero Hom by the affine normal-form basis.
5. Reverse word induction takes a finite union of shifted smaller degree
   supports. Quotient homogeneous projections kill every degree outside
   this union. The maximum absolute value in the finite support gives `B`.

## Colour finiteness

Finite crossing skeletons require no finite-colour assumption: their indices
are finite permutations and append shuffles on a fixed word. The finite-colour
hypothesis in the final unconditional theorem is used only to bound the
vacuum coefficient degrees. For an infinite colour set, coefficients at colours
absent from the boundary word are still present in the full coefficient
algebra; finite word content alone does not bound their symmetrizer degrees.
The general coefficient-bound version separates this issue explicitly.
A finite-colour restriction/transport, when needed for a larger datum, is not
proved by this module.

## Reservoir consequence and remaining comparison

`truncatedEndGSuperAlg_bounded` supplies the source support input to the
existing regular-reservoir coefficient construction. The definitions
`truncatedContentCoefficientIdeal` and
`truncatedContentModuleCoefficientIdeal` give jointly nilpotent ideals on
regular kernel and module-superfunctor Hom sectors. No graded module category
or common exponent over all contents is introduced.

`truncatedContent_isIso_of_coefficient_error` specializes existing matrix
lifting with the source support discharged. Identifying actual cup/cap
kernels, the degree-zero principal middle component of the whole augmented
inverse, and its coefficient-error membership remains separate. These
support results do not by themselves prove `CentralInvertible`.
