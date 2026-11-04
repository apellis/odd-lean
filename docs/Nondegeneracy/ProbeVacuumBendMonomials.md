# Ordered mixed-bend monomials on the whole-weight vacuum input

This is the term comparison for SwappedHomInversion §3 (4)–(5).
The input retains an arbitrary functor from the probe empty-content
module category into the full reservoir original-weight product.

`vacuumBendBlock` selects its empty reservoir block after the full output
functor is given. `vacuumBendPostTargetIso` contains, in order, the
prescribed adjacent post-Hom shift comparison, the whole-weight
following-content comparison, the stored successor-content equality,
and the regular-probe input comparison under append/restrict.

The proposed `vacuumBendPostCup_native` compares the actual
`homContentPostCup` with the raw canonical unit column. It uses the
checked post-unit chart and even naturality of that unit column for the
regular-input cast.

The proposed `vacuumBendMonomial_native` compares each actual
`homPreNegativeCap` followed by `homContentPostCup`, after regular-probe
and empty-reservoir-block evaluation, with

```
sourceIso.hom ≫ Ring.inverse shiftedPreDot ^ n ≫ shiftedPreCap
  ≫ canonicalAppend.unit ≫ restrictedDotEnd ^ r.
```

The source chart is exactly the pre-cap/pre-dot chart. The inverse power,
cap, post-unit, and post-dot are the prescribed maps. The proof does not
assume any cap, dot, unit, bend, or moment compatibility. The proposed
paired consumer uses a full tensor output family with an occupied odd
coefficient over the asymmetric two-colour fixture and arbitrary
negative and nonnegative exponents.

The padded corner isomorphisms, the odd coefficient identity
`-koszulSign(1,1)^(r+1) = (-1)^r`, and the comparison of the resulting
finite sum with `evaluatedMixedBend` are the subsequent attachment steps.
