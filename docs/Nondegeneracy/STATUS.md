# Odd nondegeneracy: results

This page lists the proved results, all on `master`; exploratory work toward extensions
belongs on `research/odd-nondegeneracy`. The written
proof is [SwappedNondegeneracy](SwappedNondegeneracy.md), the audit of the
formal statement against Brundan–Ellis is [StatementAudit](StatementAudit.md),
and the scope is [FieldScopeBoundary](FieldScopeBoundary.md). Open questions
and restart steps are in [HANDOFF](HANDOFF.md). Topic notes record local
arguments as they were written; their "open" lists and module paths do not
override this page. Every declaration below has axioms `propext`,
`Classical.choice` and `Quot.sound`, and each headline has a consumer in
`scripts/NonVacuity/` that applies it to concrete data with every hypothesis
proved.

## Main theorems

| Result | Declaration | Hypotheses | Consumer |
| --- | --- | --- | --- |
| Nondegeneracy Conjecture (BE2, arXiv:1701.04133v2, §8), homogeneous parameters | `QuiverHecke.nondegeneracy_of_symmetrizer` ([module](../../OddMath/QuiverHecke/VacuumRouteSwappedRightNegative.lean)) | Cartan superdatum with a symmetrizer (`dᵢ dᵢⱼ = dⱼ dⱼᵢ`), commutative ring with `2` invertible, `Sc.Homogeneous`, any `cs : CScalars Sc` | [SwappedRouteNondegeneracy](../../scripts/NonVacuity/SwappedRouteNondegeneracy.lean) |
| Same, every commutative ring (integral form of the presentation) | `QuiverHecke.integral_nondegeneracy_of_symmetrizer` ([module](../../OddMath/QuiverHecke/IntegralNondegeneracy.lean)) | symmetrizer, any commutative ring, homogeneous `IntegralScalars`, any `CScalars` | [IntegralNondegeneracy](../../scripts/NonVacuity/IntegralNondegeneracy.lean) |
| Inhomogeneous parameters of Brundan–Wang–Webster, arXiv:2505.22929v2, §2.2 | `QuiverHecke.bwwLowerDegreeNondegeneracy`, `QuiverHecke.bwwGradedNondegeneracy` ([module](../../OddMath/QuiverHecke/BWWNondegeneracy.lean)) | symmetrizer, `2` invertible, `Sc : BWWScalars` with `Sc.LowerDegree sy` (resp. `Sc.GradedHomogeneous sy 𝒜` over an `ℕ`-graded ring, BWW (2.6)–(2.7)), any `CScalars`; colours, weights and ring in one universe | [BWWNondegeneracy](../../scripts/NonVacuity/BWWNondegeneracy.lean) |
| All-even specialization: BWW's even basis theorem at parity zero | `QuiverHecke.bwwPolynomials_evenNondegeneracy` with BWW (2.11) checked by `quadSum_bwwPolynomials` ([module](../../OddMath/QuiverHecke/BWWEvenSpecialization.lean)); graded basis `bwwPolynomials_evenGradedNondegeneracy` (`c` in degree zero) and `bwwPolynomials_evenDirectSum` ([module](../../OddMath/QuiverHecke/BWWEvenGradedBasis.lean)) | purely even datum with a symmetrizer, `2` invertible, BWW polynomials `P` homogeneous over an `ℕ`-graded ring, any `CScalars` | [BWWEvenSpecialization](../../scripts/NonVacuity/BWWEvenSpecialization.lean) |
| Existence of normalizations | `SKM.CScalars.nonempty_of_linearIndependent`; combined: `QuiverHecke.exists_nondegeneracy_of_linearIndependent` | simple roots `ℤ`-linearly independent in the weight group | [NondegeneracyIndependentRoots](../../scripts/NonVacuity/NondegeneracyIndependentRoots.lean) |

The all-even comparison is closed by the maintainer's decision: BWW (2.11)
is checked formally and the remaining relations (2.10)–(2.15) are identified
with BWW's even 2-category by inspection; no formal comparison with an
independently formalized even 2-category for general `Q` is made
([BWWEvenComparison](BWWEvenComparison.md)). On purely even data with
Khovanov–Lauda scalars and finitely many colours the conclusion also agrees
with the even theorem `EvenBridge.nondegeneracyConjecture_of_isEven` (this
compares conclusions only).

The BWW headlines are reached through Rees parameters over `k[h]`
(`SKM.nondegeneracyConjecture_of_lowerDegree`), their truncations `K[h]/(h^N)`
(`QuiverHecke.truncatedReesNondegeneracy`, consumer
[TruncatedReesNondegeneracy](../../scripts/NonVacuity/TruncatedReesNondegeneracy.lean))
and the graded base `QuiverHecke.nondegeneracy_of_graded_base`, whose sector
inputs hold over a base graded in degrees `0, …, b`. The route-only hypothesis
`ScalarData.PureNilpotent` is supplied by the truncations and does not enter
the headlines. Plan and design: [Phase2Plan](Phase2Plan.md),
[BWWArchitecture](BWWArchitecture.md).

## Consequences

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

## Route

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
so they hold for every symmetrizable datum.

### Proof structure

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

## Scope and open questions

Symmetrizability is an intended hypothesis; nonsymmetrizable Cartan data are
out of scope. The ground ring
is purely even (BE2 allows supercommutative rings). The open question is:

- **Normalizations for dependent roots** (deferred). A normalization exists
  exactly when `Π tᵢⱼ^{nⱼ} = 1` for every `i` and every integer relation
  `Σ nⱼ αⱼ = 0` among the simple roots (`RootCover.nonempty_cScalars_iff`).
  For dependent roots the theorems can therefore be vacuous: for affine `A₁`
  with `α₀ + α₁ = 0`, `CScalars.t_mul_t_eq_one` forces `tᵢ₀ tᵢ₁ = 1`, so
  `t₀₁ = 2` admits no normalization. Brundan–Wang–Webster, Remark 2.4, allow
  arbitrary normalizations.

When `2` is not a unit the presentation includes the integral relations
`Rel.zInt`; with `2` invertible they hold automatically.

## Verification

Every integration into this branch passes the full build with warnings as
errors, the global axiom audit and the non-vacuity library on its exact head;
the pull requests record heads and runs. Finite computations in topic notes
are evidence about their instances only and are not part of the proof.
Modules of earlier routes that no retained result uses were removed, and the
cyclotomic action modules were merged into topical files; see
[Cleanup](Cleanup.md).
