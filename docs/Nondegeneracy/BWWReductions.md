# Reductions for Brundan–Wang–Webster parameters

This note records the reduction of the Brundan–Wang–Webster (BWW) Nondegeneracy Conjecture,
over arbitrary commutative rings with `2` invertible, to truncated Rees parameters. It is the
BWW analogue of `GradedParameters.lean`, `LowerDegreeParameters.lean` and
`TruncatedReesParameters.lean`. Notation follows `BWWParameters.md`.

## Checked declarations (`OddMath/SKM/BWWReesParameters.lean`)

- `BWWScalars.map`, `BWWScalars.mapCScalars`: base change of BWW parameters and of
  normalizations along a ring map.
- `BWWScalars.LowerDegree sy Sc`: every nonzero coefficient `c i j p q` with `i ≠ j`,
  `p < dᵢⱼ`, `q < dⱼᵢ` has `coefficientDegree sy i j p q ≥ 0`.
  - `lowerDegree_iff_interior`: only the interior monomials (`p, q > 0`) are constrained. Pure
    terms and the constant term always have positive coefficient degree.
  - `LowerDegree.map`, `GradedHomogeneous.lowerDegree`, `ScalarData.toBWW_lowerDegree_iff`
    (on Brundan–Ellis parameters the condition is `ScalarData.LowerDegree`).
- `BWWReesParameters.scalars sy Sc` over `k[h] = MvPolynomial Unit k`: the coefficient of
  `u^p v^q` below the corners is `c i j p q · h^{coefficientDegree}`; units and corners are
  unchanged.
  - `gradedHomogeneous`: for lower-degree `Sc` these are graded homogeneous for the degree
    grading of `k[h]`, with `k` in degree `0`. No grading of `k` is needed.
  - `map_specialize`: they specialize to `Sc` at `h = 1`.
  - In `k[h]/(h^N)` every pure coefficient is a multiple of the nilpotent central `h`.
- `BWWParameterProperty D`: a property `holds Sc cs` of BWW parameters with normalizations over
  rings with `2` invertible, stable under base change (`map`) and detected by jointly separating
  families of base changes (`separating`).
- For such a property and a symmetrizer `sy`:
  - `TruncatedReesCase`: `holds` for `(BWWReesParameters.scalars sy Sc).map (trunc k N)` for
    every `k` with `2` invertible, every lower-degree `Sc`, every normalization and every `N`.
  - `LowerDegreeCase`: `holds` for every lower-degree `Sc` over every `k` with `2` invertible.
  - `GradedCase`: `holds` for every graded-homogeneous `Sc` over every `ℕ`-graded `k` with `2`
    invertible. This is the parameter generality of BWW §2.2.
  - `lowerDegreeCase_of_truncatedReesCase`, `gradedCase_of_lowerDegreeCase`,
    `gradedCase_of_truncatedReesCase`.
- `BWWParameterProperty.interiorNondegeneracy`: the Brundan–Ellis conjecture for the interior
  part `BWWScalars.toScalars` is such a property, by `nondegeneracyConjecture_scalarChange` and
  `nondegeneracyConjecture_of_separating`.

## Target statement for the BWW assembly

Once the BWW presentation and its conjecture `BWWNondegeneracyConjecture cs` are defined for
`Sc : BWWScalars D k`, it must be shown to satisfy two things:

1. scalar change: the conjecture for `Sc` implies it for `Sc.map f`, with `mapCScalars f cs`,
   when `2` is invertible in the source;
2. separation: the conjecture for all `Sc.map (g j)`, with `g` jointly detecting zero, implies
   it for `Sc`.

Both proofs follow `GroundRingNondegeneracy.lean` and `TruncatedReesParameters.lean`: they use
basis transport through `S ⊗[R] Hom_R ≃ Hom_S` and injectivity checked after separating base
changes. They are what it takes for the conjecture to be a `BWWParameterProperty`.

The assembly target is then `TruncatedReesCase sy`, and `gradedCase_of_truncatedReesCase` gives
the BWW §2.2 generality.

## The truncated Rees case reduces to a bounded graded base

The truncated Rees case needs no universal BWW parameter ring and no fields. Over `k[h]/(h^N)`,
grade by the power of `h`, with `k` in degree `0`. This grading lives in degrees `0..N-1`. The
units sit in degree `0`, and every coefficient below the corners sits in its coefficient degree.

This is the input shape of `nondegeneracy_of_graded_base`, which is in the Stage A
truncated-Rees PR and works over an arbitrary commutative ground ring `K` with `k` graded by
`ℤ → Submodule K k` and supported in a bounded range. The remaining step, not yet checked, is the BWW
analogue of that theorem: the graded-supercategory argument with pure terms present. The
proposed argument: the pure terms of positive degree multiply dots of total degree strictly smaller than the
corner. So they should be lower-order perturbations in the dot filtration, and the leading
(homogeneous) part should be the Brundan–Ellis presentation with the same `t` and interior part.
