# Odd nondegeneracy: current mathematical status

This is the authoritative current status for `research/odd-nondegeneracy`.
The written proof is [SwappedNondegeneracy](SwappedNondegeneracy.md); the
actionable dependency order is [HANDOFF](HANDOFF.md).
Topic notes record local arguments and their original claim boundaries;
their historical “open” lists do not override this page. Earlier inventories
and checkpoint narratives remain available in git history.

**The Phase 1 odd/mixed nondegeneracy theorem is proved in Lean.**
`QuiverHecke.nondegeneracy_of_symmetrizer`
([VacuumRouteSwappedRightNegative](../../OddMath/QuiverHecke/VacuumRouteSwappedRightNegative.lean))
states: for a Cartan superdatum `D` with a symmetrizer `sy : SKM.Symmetrizer D`
(positive integers `dᵢ` with `dᵢ dᵢⱼ = dⱼ dⱼᵢ`), every commutative ring `R`
with `IsUnit (2 : R)`, every scalar system `Sc` with `Sc.Homogeneous`, and
every `cs : SKM.CScalars Sc`, `SKM.NondegeneracyConjecture cs` holds (BE2,
arXiv:1701.04133v2, §8). It has no further hypotheses; its axioms are
`propext`, `Classical.choice` and `Quot.sound`, and the concrete consumer
[SwappedRouteNondegeneracy](../../scripts/NonVacuity/SwappedRouteNondegeneracy.lean)
applies it to a mixed-parity two-colour datum with distinct symmetrizer
entries.

**Consequence: the Decategorification Conjecture (BE2 §12).**
`QuiverHecke.SerreComplex.decategorification`
([Decategorification](../../OddMath/QuiverHecke/Decategorification.lean))
applies Theorems 11.7 and 12.1 (`gammaInt_bijective`) to
`nondegeneracy_of_symmetrizer`: `γ : U̇_{q,π}(𝔤)_ℒ → K₀(𝔘̇(𝔤))` is bijective
for homogeneous parameters over a field `k` with `2 ≠ 0`, finitely many
colours, a finitely generated free weight lattice and linearly independent
roots and coroots ((10.2) is not assumed).
`decategorification_sourceWeightLattice` states it in BE2's own setting: the
weight lattice `P = {λ ∈ 𝔥* | ⟨hᵢ, λ⟩ ∈ ℤ}` of a complex realization with
linearly independent roots and coroots, an arbitrary colour set, and the route
hypothesis `DegreeLocallyFinite` of Theorem 11.7 (automatic for finitely many
colours). It comes from `decategorification_of_separating` (torsion-free weight
group, independent roots, integral weights separating the coroots) and
`gammaInt_bijective_of_nondegenerate` / `theorem_12_1_of_nondegenerate`, which
take nondegeneracy of the form of Theorem 10.1 as input. That nondegeneracy is
descended from finite weight windows in
[WindowForm](../../OddMath/CoveringQuantum/UDot/WindowForm.lean)
(`sesquilinearForm_nondegenerate_of_separating`,
`sourceWeightLattice_nondegenerate`). Beyond BE2's §12 setting the remaining
hypotheses are `2 ≠ 0` (characteristic 2 is not covered) and
`DegreeLocallyFinite`. Consumers:
[Decategorification](../../scripts/NonVacuity/Decategorification.lean),
[DecategorificationWeightLattice](../../scripts/NonVacuity/DecategorificationWeightLattice.lean)
(infinitely many odd colours on `P`).

The proof follows the swapped route. `nondegeneracy_of_swapped_bubble_fields`
(#1068) reduces the conjecture to the positive- and nonpositive-height bubble
fields on the swapped route bases. The positive-height field is proved
unconditionally (#1094). The nonpositive-height field reduces through
`SwappedRightEntriesField` to `RightVacuumEntrySupply`, and that to
`VacuumRightNegativeEntries` at every probe reservoir (#1095). Its three
fields are `vacuumEntry_neg_even` (#1086), `vacuumEntry_neg_odd` and
`vacuumEntry_odd_neg` (#1084); #1098 assembles them into
`rightVacuumEntrySupply`, `swappedRightEntriesField` and the end theorem.
The ground-ring descent to characteristic-zero fields, finite-colour
restriction and pairing-extension recovery used by the route are the checked
reductions described below.

The swapped route enters through the vacuum route of #1056:
`QuiverHecke.nondegeneracy_of_vacuum_route` proves the conjecture from
`VacuumRouteHypotheses D sy`, and `nondegeneracy_of_vacuum_route_fields`
builds those hypotheses from the bubble fields (`VacuumRouteHypotheses.of_fields`),
so they hold for every symmetrizable datum. On purely even
data with Khovanov–Lauda scalars and finitely many colours, the conclusion
matches the checked even theorem (#1059); this compares conclusions only.
Phase 2 (target stated in #1101, see the remaining critical chain) and the
full all-even comparison of [FieldScopeBoundary](FieldScopeBoundary.md)
remain open, so the branch is not complete.

**Consequences: Hom bases, `β_λ` and graded dimensions.**
[HomBases](../../OddMath/QuiverHecke/HomBases.lean) (note: [HomBases](HomBases.md))
applies `nondegeneracy_of_symmetrizer` under its hypotheses (symmetrizer,
`IsUnit (2 : k)`, homogeneous parameters). `QuiverHecke.betaSYM_bijective`
and `betaSYMEquiv`: `β_λ : SYM ≃ End(1_λ)` (surjectivity is Theorem 8.1 on the
empty boundary, `endOne_mem_bubbleSpan`, now over every commutative ring).
`MatchingBasisChoice.expansionEquiv` (right `SYM`-linear by
`expansion_mapRange_mul`), `homBasisOfSymmetrizer` with
`homBasisOfSymmetrizer_apply` (basis `f(σ, λ) β_λ(p)`, `p` a monomial of
`SYM.coefficientBasis`), `free_hom` and the graded form `componentEquiv`.
Over a field with `2 ≠ 0` and `DegreeLocallyFinite`:
`wordHomComponent_finrank_eq_sum`, `homDimension_coeff_eq_sum`, and
`homDimension_eq_form_mul_symDimension`, BE2 Theorem 12.1 (dum) without the
Nondegeneracy Conjecture as a premise. Consumer:
[HomBases](../../scripts/NonVacuity/HomBases.lean).

**Graded components of `SYM`.** The monomials of `SYM.coefficientBasis` of bidegree `z`
form a basis of the homogeneous component `SYM_z` over every commutative ring
(`SYM.componentBasis`, `OddMath/SKM/SymComponentBasis.lean`), so `dim SYM_z` is the number of
monomials of bidegree `z` over every field (`SYM.finrank_component`) and the coefficients of
`S = symDimension` in BE2 (dum) count monomials (`symDimension_coeff_eq_card`). This is the
coefficientwise form of the corrected product of ERRATA [BE2] 8. The product identity itself
is `SKM.hasProd_symFactor` / `SKM.symDimension_eq_tprod` (`OddMath/SKM/SymProductFormula.lean`):
`S` is the coefficientwise convergent product in `PowerSeries ℚ` of `(1 - q^{deg e_{i,r}})⁻¹`
over the even generators and `1 + π q^{2 d_i}` over the odd generators, under
`DegreeLocallyFinite`; composed with (dum) it is
`QuiverHecke.homDimension_eq_form_mul_tprod_symFactor`. Consumer:
[SymProductFormula](../../scripts/NonVacuity/SymProductFormula.lean).

## Scope

**Phase 1:** symmetrizable data and homogeneous admissible parameters.
**Phase 2:** after Phase 1, pursue inhomogeneous parameters while retaining
symmetrizability. **Nonsymmetrizable Cartan data are out of scope.**
The branch is complete once the odd theorem and its checked all-even
specialization match the most general cited even nondegeneracy theorems,
except for requiring 2 invertible in the base ring. The graded-coefficient
parameter benchmark and exact completion criteria are in
[FieldScopeBoundary](FieldScopeBoundary.md). Phase 2 is not yet established.

The proposed construction uses a purely even field with 2 invertible,
compatible symmetrizable Cartan superdata with positive integral symmetrizers,
homogeneous admissible parameters with separate odd-variable exponent support
and the specified leading units, and supplied `cs : CScalars Sc`.
It includes connected data, repeated colours and arbitrary colour sets.

**Ground-ring descent is already formalized.**
`SKM.nondegeneracyConjecture_of_charZeroField` in
[GroundRingNondegeneracy](../../OddMath/SKM/GroundRingNondegeneracy.lean)
reduces every ordinary commutative ring with 2 invertible to the
characteristic-zero field case for the same datum and homogeneous parameters.
It requires no domain, reducedness, flatness, finite-colour or independent-root
hypothesis on the target ring. Thus proving that field input supplies the
ordinary-ring conclusion; no additional ground-ring descent remains.
The field input is supplied by the swapped route (top of this page). This reduction retains the datum and
homogeneity conditions and does not address genuinely supercommutative
base rings or existence of CScalars for every weight realization.
Intermediate lemmas may have broader scope. The field predicate fixes the datum;
the swapped-route construction with a supplied positive symmetrizer
therefore establishes Phase 1. Symmetrizability is not implied by `Datum`,
homogeneous parameters or supplied normalizations, and will remain an intended
hypothesis. Relaxing parameter homogeneity belongs to Phase 2; proving the
broader nonsymmetrizable §8 conjecture is not a branch obligation.

## Proof structure

The written argument is [SwappedNondegeneracy](SwappedNondegeneracy.md). In
Lean the end theorem is assembled from the following reductions and inputs;
each declaration carries its exact hypotheses.

| Step | Declarations | Module |
| --- | --- | --- |
| Ground ring: every commutative ring with `2` invertible reduces to characteristic-zero fields | `SKM.nondegeneracyConjecture_of_charZeroField`, `nondegeneracyConjecture_scalarChange` | [GroundRingNondegeneracy](../../OddMath/SKM/GroundRingNondegeneracy.lean) |
| Orientation: full nondegeneracy is upward independence at every weight | `nondegeneracy_iff_upward_independence` | [UpwardNondegeneracyReduction](../../OddMath/SKM/UpwardNondegeneracyReduction.lean) |
| Colours: finite-colour restrictions suffice | `nondegeneracy_of_restrictColours_upward` | [FiniteColourNondegeneracy](../../OddMath/QuiverHecke/FiniteColourNondegeneracy.lean) |
| Vacuum route: nondegeneracy from route sectors on the pairing extensions of finite-colour restrictions | `nondegeneracy_of_vacuum_route_sectors`, `nondegeneracy_of_vacuum_route` | [VacuumRouteNondegeneracy](../../OddMath/QuiverHecke/VacuumRouteNondegeneracy.lean) |
| Vacuum-route hypotheses from the bubble fields | `VacuumRouteHypotheses.of_fields`, `nondegeneracy_of_vacuum_route_fields` | [VacuumRouteFields](../../OddMath/QuiverHecke/VacuumRouteFields.lean) |
| Reduction to the bubble fields on the swapped route bases | `nondegeneracy_of_swapped_bubble_fields` | [VacuumRouteSwappedCharts](../../OddMath/QuiverHecke/VacuumRouteSwappedCharts.lean) |
| Positive-height bubble field, through the left vacuum entries | `swappedLeftEntriesField`, `positiveBubbleField_swappedRouteBases` | [VacuumRouteSwappedPositiveField](../../OddMath/QuiverHecke/VacuumRouteSwappedPositiveField.lean) |
| Nonpositive-height bubble field, through the right vacuum entries | `SwappedRightEntriesField`, `RightVacuumEntrySupply`, `VacuumRightNegativeEntries` | [VacuumRouteSwappedNonpositiveField](../../OddMath/QuiverHecke/VacuumRouteSwappedNonpositiveField.lean), [VacuumRouteSwappedRightField](../../OddMath/QuiverHecke/VacuumRouteSwappedRightField.lean) |
| Right vacuum entries at negative height | `vacuumEntry_neg_even`, `vacuumEntry_neg_odd`, `vacuumEntry_odd_neg` | [SupportedVacuumRightEntriesEven](../../OddMath/QuiverHecke/SwappedAssembly/SupportedVacuumRightEntriesEven.lean), [SupportedVacuumRightEntriesOdd](../../OddMath/QuiverHecke/SwappedAssembly/SupportedVacuumRightEntriesOdd.lean) |
| Assembly | `rightVacuumEntrySupply`, `swappedRightEntriesField`, `nondegeneracy_of_symmetrizer` | [VacuumRouteSwappedRightNegative](../../OddMath/QuiverHecke/VacuumRouteSwappedRightNegative.lean) |

The upward module action is built on the cyclotomic quotients of the
quiver Hecke supercategory with exterior coefficients (`CyclotomicAction`,
`SwappedAssembly`); the swapped route evaluates it at a probe reservoir whose
cutoffs are chosen large enough for the half-turn windows to be injective.

Normalizations: `CScalars` is an argument of the end theorem. A choice exists
whenever the simple roots are `ℤ`-linearly independent in the weight group
(`SKM.CScalars.nonempty_of_linearIndependent`), and
`QuiverHecke.exists_nondegeneracy_of_linearIndependent` combines the two.

Modules of earlier routes that no retained result uses were removed; see
[Cleanup](Cleanup.md).

## Remaining critical chain

Phase 1 is proved (see the top of this page). The remaining obligations of
the branch are those of [FieldScopeBoundary](FieldScopeBoundary.md):

1. **Phase 2.** Inhomogeneous parameters for symmetrizable data, at least
   the graded-coefficient generality of Brundan–Wang–Webster,
   arXiv:2505.22929v2, Theorem 5.6, and its underlying ungraded basis
   statement. Neither the present homogeneous proof nor its ground-ring
   reduction is known to supply this. The target is stated as
   `SKM.GradedCoefficientNondegeneracy D sy`
   ([GradedParameters](../../OddMath/SKM/GradedParameters.lean), #1101):
   nondegeneracy for parameters over `ℕ`-graded rings with `2` invertible
   whose coefficient `sᵢⱼ^{pq}` lies in degree `2(dᵢdᵢⱼ - dᵢp - dⱼq)`.
   `SKM.nondegeneracyConjecture_of_lowerDegree` proves that it implies the
   conjecture for every lower-degree (in particular every homogeneous)
   parameter system over a commutative ring with `2` invertible, through the
   Rees family over `k[h]` specialized at `h = 1`; consumer
   [GradedParameters](../../scripts/NonVacuity/GradedParameters.lean), on
   inhomogeneous parameters `u³ + uv + v³`. BE2's `Scalars` now carry the whole box of coefficients below the corners, including the
   pure monomials `u^r` and `v^s` that Brundan–Wang–Webster allow (decision: generalize in
   place, [BWWArchitecture](BWWArchitecture.md)); BE2's printed parameters are the case
   `ScalarData.NoPure`. The probe dot units take the route-only hypothesis
   `ScalarData.PureNilpotent` (pure coefficients in a nilpotent ideal), supplied by
   homogeneous parameters (`NoPure.pureNilpotent`) and by the truncated Rees parameters
   (`BWWReesParameters.truncated_pureNilpotent`); it does not enter the target statement.
   The target is reduced, by ring maps
   that ignore grading, to its universal instance
   (`LowerDegreeParameters.gradedCoefficientNondegeneracy_iff`), to
   lower-degree parameters over characteristic-zero fields
   (`gradedCoefficientNondegeneracy_of_charZeroField`) and to the Rees
   parameters truncated to `K[h]/(h^N)`
   (`gradedCoefficientNondegeneracy_of_truncated`), whose remaining
   hypothesis `TruncatedRees.TruncatedReesNondegeneracy D sy` is open.
   Grading infrastructure for that case (Phase2Plan, step 2, items 1–3):
   coefficient-graded parts of presented Hom groups
   (`Diagrams.CoefficientGrading.presentedPart`, independence and spanning
   for homogeneous presentations), homogeneity of the quiver Hecke
   presentation with graded parameters
   (`QuiverHecke.isHomogeneous_coefficientGraded`, Rees case
   `QuiverHecke.isHomogeneous_rees`) and restriction of scalars
   (`Diagrams.Supercategory.restrictScalars`), bundled as a
   `GradedSupercategory K` (`Diagrams.CoefficientGrading.gradedSupercategory`;
   the quiver Hecke case over `K[h]`: `QuiverHecke.reesGradedSupercategory`);
   consumer [CoefficientGrading](../../scripts/NonVacuity/CoefficientGrading.lean).
   The truncations `K[h]/(h^N)`: `QuiverHecke.truncGradedAlgebra`,
   `QuiverHecke.truncatedReesGradedSupercategory`. Open: the field-route
   arguments over these bases (step 2, item 4). Plan, comparison and design: [Phase2Plan](Phase2Plan.md).
2. **All-even comparison.** A checked comparison at parity identically zero
   recovering the benchmark's ordinary basis theorem: presentations,
   normalizations, decorated matching families and bubble coefficients, and
   the grading. #1059 compares conclusions only, for Khovanov–Lauda scalars
   and finitely many colours.
3. **Normalizations.** `CScalars` is supplied to the end theorem. A choice
   exists whenever the simple roots are linearly independent over `ℤ` in the
   weight group (`SKM.CScalars.nonempty_of_linearIndependent`, combined with
   the end theorem in `QuiverHecke.exists_nondegeneracy_of_linearIndependent`),
   which includes Brundan–Ellis's setting. Benchmark realizations with
   dependent roots still need compatible normalizations or a
   change-of-normalization comparison. **Open (gap recorded, deferred):** a
   normalization exists exactly when `Π tᵢⱼ^{nⱼ} = 1` for every `i` and every
   integer relation `Σ nⱼ αⱼ = 0` among the simple roots
   (`RootCover.nonempty_cScalars_iff`). For dependent roots the theorem can
   therefore be vacuous: for affine `A₁` with `α₀ + α₁ = 0` it forces
   `tᵢ₀ tᵢ₁ = 1` (`CScalars.t_mul_t_eq_one`), so `t₀₁ = 2` admits no
   normalization. Brundan–Wang–Webster, Remark 2.4, allow arbitrary
   normalizations; covering that case is not attempted.

The audit of the formal statement against Brundan–Ellis §8, and the precise
scope of the even specialization, are in [StatementAudit](StatementAudit.md).

The sector inputs of the vacuum route are supplied by the swapped bubble fields
(`VacuumRouteHypotheses.of_fields`).

## Verification

Every integration into this branch passes the full build with warnings as
errors, the global axiom audit (`propext`, `Classical.choice`, `Quot.sound`)
and the non-vacuity library on its exact head; the pull requests record heads,
runs and merge commits. Finite computations in earlier notes are evidence about
their instances only and are not part of the proof.
