# Research scope, field input and the even benchmark

## Branch goal and phases

The goal of `research/odd-nondegeneracy` is the odd/mixed analog of the most
general known ordinary even nondegeneracy theorems, with the following order.

1. **Phase 1 (current):** prove nondegeneracy for symmetrizable Cartan superdata
   and homogeneous admissible parameters over ordinary commutative rings with
   2 invertible. Retain the odd-row evenness condition, separate odd-variable
   exponent support, prescribed leading units and compatible `CScalars`.
   The integral form extends Phase 1 to every commutative ring (see
   "Integral form" below).
2. **Phase 2 (after Phase 1):** pursue inhomogeneous parameters, still for
   symmetrizable data, until the parameter generality of the even benchmark
   below is covered. Do not assume that the present graded proof or its
   ground-ring reduction automatically supplies this extension.

**No proof for nonsymmetrizable Cartan data is pursued on this branch.**
Symmetrizability is an intended hypothesis in both phases. Further generality
beyond the even benchmark is not a completion requirement. This scope governs
all research documentation; historical open-step lists do not enlarge it.

## Even benchmark and the meaning of inhomogeneous

The comparison is full nondegeneracy for the ordinary Kac–Moody 2-category,
including mixed upward/downward Hom spaces and bubble coefficients.

- [Webster, arXiv:1603.06311v4](https://arxiv.org/pdf/1603.06311v4),
  §2 and Theorem 3.13: the Cartan datum is symmetrizable; parameters are
  homogeneous. The printed ring theorem requires invertible symmetrizers.
- [Brundan–Wang–Webster, arXiv:2505.22929v2](https://arxiv.org/pdf/2505.22929v2),
  Conventions, §§2.1–2.2 and Theorem 5.6: the ordinary 2-quantum-group basis
  theorem uses symmetrizable data and an N-graded commutative coefficient ring,
  with homogeneous Q-polynomials for the total grading. Positive-degree
  coefficients allow terms of lower weighted dot degree. This theorem does
  not require the symmetrizers to be units. Its root-datum hypotheses include
  local finiteness and independent simple coroots.

Phase 1 puts base coefficients in degree zero, as in `Scalars.Homogeneous`.
Phase 2 must at least cover the graded-coefficient parameter generality in the
second reference and the corresponding underlying ungraded basis statement.
Here “inhomogeneous” means relaxing the Phase 1 condition on weighted dot
degrees; the benchmark still has a total grading. Arbitrary polynomials with
no compatible grading or degree bounds are not asserted to be known in the
even literature, and proving that larger class is not required to finish.
The precise extension of the current `Scalars` presentation and any scalar
specialization argument must be proved, not inferred from the terminology.

## Completion criterion and all-even specialization

The branch is done when the verified odd/mixed theorem covers the cited even
benchmark's admissible parameters, root/weight realizations and base rings,
with the sole additional base-ring requirement that 2 be invertible, and a
checked comparison at parity identically zero recovers its ordinary even
basis theorem. “All Cartan data” here means all symmetrizable data allowed
by that benchmark, not nonsymmetrizable matrices.

The comparison must identify presentations, normalization conventions,
decorated matching families and bubble coefficients, and recover the graded
statement when the benchmark includes grading. A KL-only parameter example
or the positive-half PBW theorem does not meet this criterion. Extra proof
premises such as a supplied detecting action or vacuum observation must be
discharged. Required builds, axiom audits and concrete consumers must pass.

Supplied `CScalars` remain part of the current formulation. To claim recovery
for every benchmark datum, supply the compatible normalizations under its
realization hypotheses or prove the relevant change-of-normalization
comparison. Do not assume they exist for arbitrary collapsed weight data.
No theorem over genuinely supercommutative base rings or realizations
beyond the even benchmark is required by this branch goal. Rings where 2 is
not a unit are covered by the integral form below.

## Source boundary and existing field reduction

Brundan–Ellis, *Super Kac–Moody 2-categories*,
[arXiv:1701.04133v2](https://arxiv.org/pdf/1701.04133v2), §8,
states a broader conjecture than this branch's chosen target. The
symmetrizability and homogeneity assumptions on pp.8–9 apply to the remainder
of the introduction, and Section 9 introduces them again. This scope decision
is not an erratum to that conjecture or a claim to prove its entire scope.

`Datum` in `SKM/Basic.lean` does not supply a `Symmetrizer`, and
`Scalars.Homogeneous` does not imply one. For example, the all-odd pattern

```
  2  -2  -4
 -4   2  -2
 -2  -4   2
```

has even rows, but its symmetrizer equations force d₁=2d₂, d₂=2d₃ and
d₃=2d₁, contradicting positivity. Such data are outside the research target;
no additional Lean counterexample construction is claimed here.

For Phase 1, fix `D` and `sy : Symmetrizer D`, and prove
`CharZeroFieldNondegeneracy D`. This predicate quantifies over every
characteristic-zero field, homogeneous `Sc` and supplied `CScalars Sc` for D.
`nondegeneracyConjecture_of_charZeroField` is already proved and supplies the
ordinary commutative-ring conclusion with 2 invertible. There is no remaining
Phase 1 ground-ring descent obligation. The reduction retains the datum and
parameter restrictions; it does not establish Phase 2.

The current full-ELV route has no extra even-height restriction. In the
balanced schedule the probe level P is even and the reservoir level is
N=P−hᵢ(μ), so N has the required parity. `ReservoirWeights.reservoir_parity`
and the odd-pairing invariant retain the original weight coset. Both weighted
component matrix-inverse APIs accept arbitrary cutoff parity; the
polynomial-cap consumer includes occupied odd cutoff five. The older
even-cutoff action note describes a narrower candidate. The chosen native factors, canonical all-height distinct left mate and
complete supported action are now scoped-checked. The remaining field input
requires their vacuum/layer/bubble observations, affine and bubble
compatibility of the checked original-datum action pullback, and bounded
recovery; see STATUS.

## Integral form

When 2 is not a unit, the presentation of Definition 1.5 is replaced by its
integral form: `ScalarData D k P` carries the parameters with an arbitrary
condition `P` on 2 (`Scalars` is `P = IsUnit 2`, `IntegralScalars` is
`P = True`), and the relations `Rel.zInt` are imposed exactly at odd colours
when 2 is not a unit. Over rings with 2 invertible they hold automatically
(`relation_zInt_of_scalars`), so nothing changes there. The spanning proof
(Theorem 8.1) runs for every `P`. `SKM.IntegralNondegeneracy` deduces the
conjecture over the integral universal parameter ring from the one over the
universal ring with 2 inverted (the coefficient map is injective), then
specializes to every commutative ring;
`QuiverHecke.integral_nondegeneracy_of_symmetrizer` is the resulting
statement for symmetrizable data and homogeneous `IntegralScalars`.
`scripts/NonVacuity/IntegralNondegeneracy.lean` applies it over `ZMod 2` with
an odd colour.
