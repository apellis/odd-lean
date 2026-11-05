# Phase 2: inhomogeneous parameters

Phase 1 proves the nondegeneracy conjecture for symmetrizable Cartan superdata and
homogeneous admissible parameters (`OddMath.QuiverHecke.nondegeneracy_of_symmetrizer`,
under `Scalars.Homogeneous`, BE2 (1.31)). Phase 2 removes homogeneity for symmetrizable
data. The benchmark is Brundan–Wang–Webster, arXiv:2505.22929, Theorem 5.6, which proves
nondegeneracy in the purely even case for parameters with coefficients in an ℕ-graded ring.

## Target statement

`OddMath/SKM/GradedParameters.lean` states the target as a proposition.

- `coefficientDegree sy i j p q = 2(dᵢ dᵢⱼ - dᵢ p - dⱼ q)` is the degree that a coefficient
  `sᵢⱼ^{pq}` needs for the polynomial `Qᵢⱼ(u, v)` to be homogeneous of total degree
  `2 dᵢ dᵢⱼ` when `u` has degree `2dᵢ` and `v` has degree `2dⱼ`. It is symmetric under
  `(i, j, p, q) ↦ (j, i, q, p)` (`coefficientDegree_symm`).
- `Scalars.GradedHomogeneous sy 𝒜 Sc`: for an ℕ-grading `𝒜` of the ground ring, every
  `tᵢⱼ` lies in degree 0, and every nonzero `sᵢⱼ^{pq}` lies in degree
  `coefficientDegree sy i j p q`. This degree is then nonnegative.
- `Scalars.LowerDegree sy Sc`: every nonzero `sᵢⱼ^{pq}` has `coefficientDegree ≥ 0`. This
  is the ungraded class: the monomials of `Qᵢⱼ` that are allowed in the graded setting are
  exactly those of degree at most the leading degree.
- `GradedCoefficientNondegeneracy D sy`: for every ℕ-graded commutative ring `k` with 2
  invertible, every `Sc` satisfying `GradedHomogeneous` and every compatible `cs`, the
  nondegeneracy conjecture holds.

Checked consequences in the same file:

- `Scalars.Homogeneous.coefficientDegree_eq_zero`: a homogeneous parameter has coefficient
  degree 0 at each nonzero coefficient, so Phase 1 parameters satisfy `LowerDegree`
  (`Scalars.Homogeneous.lowerDegree`) and are `GradedHomogeneous` for the trivial grading.
- `ReesParameters.scalars sy Sc`: over `k[h]`, replace `sᵢⱼ^{pq}` by `sᵢⱼ^{pq} h^{deficit}`
  with `deficit = coefficientDegree`. For `LowerDegree` parameters this is `GradedHomogeneous`
  for the polynomial grading (`ReesParameters.gradedHomogeneous`), and its specialization at
  `h = 1` returns `Sc` (`ReesParameters.scalarChange_specialize`).
- `nondegeneracyConjecture_of_lowerDegree`: the target implies nondegeneracy for every
  `LowerDegree` parameter over a ring with 2 invertible, by the Rees family and
  `nondegeneracyConjecture_scalarChange`.

## Comparison with BWW Theorem 5.6

| BWW Thm 5.6 | Target | Status |
|---|---|---|
| Symmetrizable Cartan datum | `Symmetrizer D` | same |
| Purely even data | Cartan superdata with parity | the target is more general |
| Ground ring ℕ-graded, commutative | `GradedRing 𝒜` | same |
| `tᵢⱼ` a unit in degree 0 | `tᵢⱼ ∈ 𝒜 0` (units by `Scalars`) | same |
| `Qᵢⱼ` homogeneous of the leading degree | `GradedHomogeneous` | see the gap below |
| Coefficient monomials `u^r v^s` for `0 ≤ r < -aᵢⱼ`, `0 ≤ s < -aⱼᵢ` | BE2 `Scalars` has `s` only for `0 < p < dᵢⱼ`, `0 < q < dⱼᵢ` | **gap** |
| No restriction on 2 | `IsUnit 2` | intended Phase 2 hypothesis |
| Root datum hypotheses of BWW | the BE2 weight lattice of `D` | as in Phase 1 |
| Compatible bubble parameters | `cs : CScalars Sc` supplied | as in Phase 1 |

**Gap in the parameter range.** BE2's `Scalars` carries the mixed coefficients `sᵢⱼ^{pq}`
only for `p` and `q` both positive. BWW also allow the monomials with `p = 0` or `q = 0`
(other than the leading pair `u^{dᵢⱼ}`, `v^{dⱼᵢ}`), in positive degree. Those polynomials
cannot be expressed in the current `Scalars` structure. So `GradedCoefficientNondegeneracy`
covers BWW's class restricted to the BE2 parameter shape. Covering the rest requires an
extended parameter structure and a check that the BE2 relations and the Phase 1
constructions accept it. That is a decision about the statement, recorded here as open.

## Why the associated graded alone does not suffice

Filter the algebra by degree. The associated graded algebra is a quotient of the algebra
with the leading (homogeneous) parameters, so a basis theorem for the homogeneous algebra
gives only an upper bound for the inhomogeneous one. That gives spanning, which is already
known (`nondegeneracyConjecture_iff_injective`). Independence would need the Rees family over
`k[h]` to be `h`-torsion free, which is equivalent to the conclusion. The usable reduction
goes the other way: graded-homogeneous parameters over `k[h]` imply the inhomogeneous case
by specialization at `h = 1`, as in `nondegeneracyConjecture_of_lowerDegree`.

## Route to the target

The Phase 1 proof uses homogeneity only through the grading of the supercategory
(`isHomogeneous_gdeg`, `gradedSupercategory`), but that grading is load-bearing: it gives
nilpotence of positive-degree elements in truncated categories, degree bounds on cyclotomic
kernels, and degree bounds on inverse matrix entries. Each of these survives if the base
ring is graded, with its degree-0 part a characteristic-zero field and positive-degree
coefficients nilpotent. The plan:

1. Reduce the target to the universal graded parameter ring (polynomial coefficients with
   the coefficient degrees above, units adjoined for `t`), then to finite truncations over a
   characteristic-zero field `K`. **Done** (see "Step 1: checked reductions" below): the
   target is equivalent to its universal instance, reduces to lower-degree parameters over
   characteristic-zero fields, and from there to the Rees parameters truncated to
   `K[h]/(h^N)`, which are Artinian, finite over `K`, with nilpotent positive part.
2. Generalize the grading layer so that ring elements may carry positive degree, then
   recheck the degree arguments of the field route over such a base.
3. Rerun the detection and inverse-degree arguments of Phase 1 with base coefficients of
   positive degree, which behave like the existing truncated coefficient generators.
4. Descent to ordinary commutative rings with 2 invertible, as in Phase 1.
5. All-even specialization and comparison with BWW Theorem 5.6.

Main risks: the grading refactor touches every degree computation of the field route; the
Phase 1 arguments that use that the base is a field (dimension counts, inverses) must be
replaced by arguments over Artinian bases; the parameter-range gap above.

## Step 1: checked reductions

All maps below are ring maps along which the conjecture transfers; none uses a grading.

* `LowerDegreeParameters` (`OddMath/SKM/LowerDegreeParameters.lean`): the universal
  lower-degree parameter ring, a polynomial ring in one variable per allowed slot
  `(i, j, p, q)` (`sᵢⱼ^{pq} = sⱼᵢ^{qp}` identified) over the universal unit ring, graded by
  coefficient degree (`grading`, `gradedHomogeneous`).
  `nondegeneracyConjecture_of_universal` specializes it to every lower-degree system, and
  `gradedCoefficientNondegeneracy_iff` identifies `GradedCoefficientNondegeneracy D sy`
  with its universal instance.
* `CharZeroFieldLowerDegreeNondegeneracy D sy` and `universal_nondegeneracy`: the universal
  instance follows from the case of lower-degree parameters over characteristic-zero
  fields, through the prime fraction fields of the rationalized universal ring, which is
  reduced; `gradedCoefficientNondegeneracy_of_charZeroField`.
* `nondegeneracyConjecture_of_separating` (`OddMath/SKM/TruncatedReesParameters.lean`):
  the conjecture over `R` follows from the conjecture after base change along any family of
  ring maps that jointly detect zero. `TruncatedRees.trunc_separate`: the truncations
  `K[h] → K[h]/(h^N)` jointly detect zero. `TruncatedReesNondegeneracy D sy` (the
  conjecture for `ScalarChange.cScalars D (trunc K N) (ReesParameters.cScalars sy cs)`
  over every characteristic-zero field `K`, lower-degree `Sc` and `N`) implies the field
  case (`charZeroFieldLowerDegree_of_truncated`) and the target
  (`gradedCoefficientNondegeneracy_of_truncated`).

So the remaining Phase 2 statement is `TruncatedReesNondegeneracy D sy`: KLR parameters over
`R = K[h]/(h^N)` whose coefficients `sᵢⱼ^{pq} h^{deg}` have positive degree, with `h` of
degree one and nilpotent.

## Step 2 design: grading over the degree-zero field

**Where the grading lives now.** `StringDiagrams.GradedSupercategory R C` grades each Hom
module by `R`-submodules `degree X Y n`, so every scalar has degree zero. The KLR grading
comes from a homogeneous presentation: `OddMath/QuiverHecke/Grading.lean` proves
`isHomogeneous_gdeg Sc hc` (the defining relations lie in single degrees for `gdeg`; `hc`
is used only in the `quadNe` and `braidEq` cases, to put the monomials `sᵢⱼ^{pq} u^p v^q`
in degree `2dᵢdᵢⱼ`), then `Presentation.isInternal_homDeg` (string-diagrams-lean
`StringDiagrams/Grading.lean`) gives `isInternal_homDegree`, `gradedSupercategory D sy Sc hc`
and `gradedMonoidalSupercategory`. Everything downstream receives `hc : Sc.Homogeneous`
only to build this grading: about 30 files use `gradedSupercategory`, `HGr` or
`isHomogeneous_gdeg` directly, 15 more the ELV coefficient grading (`ELVHomGrading`,
`elvHomDegree`), and about 370 files thread `hc` through.

**Design (restriction of scalars; `GradedSupercategory` unchanged).** For
`R = K[h]/(h^N)` the grading is a `K`-linear grading, not an `R`-linear one. Keep the class
as it is and grade the `R`-linear KLR category as a `K`-linear supercategory:

1. *Generic coefficient-graded presentations* (generic diagrammatics; first on the research
   branch in odd-lean, later upstream to string-diagrams-lean `StringDiagrams/Grading.lean`).
   For `[Algebra K R]` and a graded algebra `𝒜 : ℤ → Submodule K R`, define
   `LinDiagram.homDegOf 𝒜 a b d` (combinations `Σ r_x x` with `r_x ∈ 𝒜 (d - deg x)`),
   `Presentation.IsGradedHomogeneous 𝒜 deg` and `isInternal_homDegOf`, as `K`-submodules.
   For the trivial grading (`𝒜 0 = ⊤`, `K = R`) these are `homDeg`, `IsHomogeneous`,
   `isInternal_homDeg`; prove that agreement once so that the Phase 1 statements are
   recovered.
   *Checked* (`OddMath/Diagrams/CoefficientGrading.lean`, as additive subgroups):
   `CoefficientGrading.part`, `component`, `IsHomogeneous`, `component_mem_ideal` (the tensor
   ideal of a coefficient-graded homogeneous presentation is homogeneous),
   `presentedPart`, `iSup_presentedPart`, `iSupIndep_presentedPart` (each Hom group of the
   presented category is the internal direct sum of its homogeneous parts) and
   `smul_mem_presentedPart` (closure under `𝒜 0`). Open in item 1: the `K`-submodule form
   (needs item 2) and the comparison with the trivial grading.
2. *Restriction of scalars for supercategories*: `Linear K C` and `Supercategory K C` from
   `Supercategory R C` and `Algebra K R` (parity projections are `R`-linear, hence
   `K`-linear). New file, about 100 lines; no existing file changes.
   *Checked* (`OddMath/Diagrams/RestrictScalars.lean`): `Linear.restrictScalars` and
   `Supercategory.restrictScalars`, as definitions (not instances) to avoid diamonds at
   `K = R`.
3. *KLR grading* (`OddMath/QuiverHecke/Grading.lean`): `isGradedHomogeneous_gdeg` from
   `Sc.GradedHomogeneous sy 𝒜` (the same case split; `hc` replaced by membership of
   `sᵢⱼ^{pq}` in `𝒜 (coefficientDegree)` and of `tᵢⱼ` in `𝒜 0`), then
   `gradedSupercategoryOf 𝒜 : GradedSupercategory K (H D Sc)` and its monoidal version, with
   `gradedSupercategory D sy Sc hc` the special case `K = R`, trivial grading.
   *Checked* (`OddMath/QuiverHecke/CoefficientGrading.lean`): `isHomogeneous_coefficientGraded`
   (the quiver Hecke presentation is coefficient-graded homogeneous when the `tᵢⱼ` lie in
   `𝒜 0` and each nonzero `sᵢⱼ^{pq}` lies in `𝒜 (coefficientDegree)`, indexed by `ℤ`),
   `iSupIndep_coefficientGraded`, and `isHomogeneous_rees` (the Rees parameters of a
   lower-degree system over `K[h]`, `h` in degree `1`). Open: the bundled
   `GradedSupercategory K` structure (needs item 2) and the truncations `K[h]/(h^N)`
   (needs the coefficient grading of the quotient ring).
4. *Downstream threading*: the ELV coefficient grading (`ELVHomGrading`, `ELVOldGrading`,
   `ELVOldCategoryGrading`, `ELVLowerDegree`, `ELVKernelDegree`, `ELVKernelBoundaryDegrees`,
   `ELVWeightedKernelBoundaryCoordinates`, `ELVTruncatedNilpotence` and the other files
   that use `elvHomDegree`), then the files carrying `hc`. The edit is uniform: replace
   `(hc : Sc.Homogeneous)` by `[GradedAlgebra 𝒜] (hc : Sc.GradedHomogeneous sy 𝒜)`, degrees
   over `k` by degrees over `K`.

**Why the field arguments survive.** `R = K[h]/(h^N)` is finite over `K`, so every graded
piece is a finite-dimensional `K`-space, and an `R`-linear map is injective if and only if
it is as a `K`-linear map. The Phase 1 dimension counts and inverse-degree bounds can then
run over the field `K`: a free `R`-module of rank `r` has `K`-dimension `N r`, and `h`
behaves like the existing positive-degree ELV coefficient generators (degree one,
nilpotent). What must be rechecked are the places that invert scalars of `R` or use that
the base is a field. Units of `R` are `K^× + hR`, so a scalar of degree zero is invertible
exactly when it is nonzero in `K`.

**Containment.** Items 1–3 are contained: three new or changed files, no change to an
existing class, and the Phase 1 grading recovered by specialization. Item 4 is not: it is a
uniform but broad change across the ELV route (hundreds of files), and it needs the
field-only steps rechecked. Order: land 1–3 with a non-vacuity check that the Rees
truncated parameters give a `GradedSupercategory K`, then audit which Phase 1 steps use that
the base is a field (rather than only that the degree-zero part is one), and only then
thread item 4.

