# Odd nondegeneracy: mathematical handoff

## Research objective and order

Finish **Phase 1**, the symmetrizable homogeneous-parameter theorem, using
the dependencies below and the already-proved ground-ring reduction. Then
begin **Phase 2**, inhomogeneous parameters for symmetrizable data. Do not
pursue nonsymmetrizable Cartan data. Stop when the odd analog and its checked
all-even specialization recover the most general cited even nondegeneracy
theorems over rings with 2 invertible; see
[FieldScopeBoundary](FieldScopeBoundary.md) for the parameter benchmark and
completion checks. Phase 2 does not block completion of the Phase 1 proof.

Start with [STATUS](STATUS.md) for established scope and claim boundaries.
[SwappedNondegeneracy](SwappedNondegeneracy.md) is the proposed written proof.
This file records next mathematical dependencies, not session telemetry.

## Proposed argument restart trees

The exact source trees below are reachable from this research branch in
history only. They include unfinished source and concrete consumer drafts;
no proposed source is imported. Each linked commit contains a full source
tree. Its stated scope is separate from full integration verification.
For integration, restore the topical source, consumer and note onto a fresh
branch from current `research/odd-nondegeneracy`; retain the current shared
library prefix and add the needed exports. Do not merge a preserved full
tree as an implementation change.
The complete inventory of preserved topic variants is in
[ResearchHistory](ResearchHistory.md#complete-argument-source-variants).

| Argument | Preserved source tree | Scope at snapshot |
| --- | --- | --- |
| Probe relations and selected vacuum attachment | [418df8069e](https://github.com/apellis/odd-lean/commit/418df8069eb8cbc07b48201ad4fccde9907b3f59) (complete source tree) | Evaluated local-record, representative tensor-comparison, global braid, selected reservoir-value and vacuum-dot drafts remain unverified. Whole-Hom word coordinates await fresh checks. The source also includes separately scoped-checked local records, reservoir presentation, path functor, dot units, signed slides and content braids awaiting their own full integration. Restore topical files only. |
| Probe and vacuum assembly successors | [82ddc2011b](https://github.com/apellis/odd-lean/commit/82ddc2011bb42715e1c5fb03359271160fa38a45) (complete source tree) | Whole-weight dot inverse producer passes; its occupied induced-vector consumer remains pending. Evaluated/weight crossing and adjacent local-record drafts are unverified. The reservoir-word comparison producer passes, but its complete factor consumer and vacuum-dot attachment remain pending. Restore only topical files and recheck; the tree also contains separately scoped-checked adjunction/dot, old braid, evaluated distinct-mate and pair-induction sources awaiting integration. |
| Whole weight probe dot inverse | [b9d9298e04](https://github.com/apellis/odd-lean/commit/b9d9298e04ce7847dac48e8d8574b5c1123befa4) (`OddMath/QuiverHecke/CyclotomicAction/ELVProbeWeightDotUnit.lean`) | Unverified whole-weight unit draft; repair the omit/docstring syntax and remaining transport details, then check the entire producer and a concrete consumer. |
| Adjacent old local record | [2cf3ffed79](https://github.com/apellis/odd-lean/commit/2cf3ffed792429c5f532e5d94b58da8dbd66d4aa) (`OddMath/QuiverHecke/CyclotomicAction/ELVInductionGridRelations.lean`) | Native module slides pass; the final two whole-Pi lifts remain unverified. Generic and concrete adjacent local constructors await complete paired checks. |
| Native multicolour structure | [3a6240c6bd](https://github.com/apellis/odd-lean/commit/3a6240c6bdac98cfddc4f55a2614f73b96d2f894) (`OddMath/QuiverHecke/CyclotomicAction/ELVRouquierMulticolour.lean`) | All seven chosen original-parameter fields and a concrete consumer passed scoped checks; fresh publication repeat and full integration remain separate gates. |
| Chosen whole-Hom word coordinates | [6d07efe699](https://github.com/apellis/odd-lean/commit/6d07efe699314d60e0bcd12b685122434e62be3b) (`OddMath/QuiverHecke/CyclotomicAction/ELVPowerWordHomCoordinates.lean`) | Producer and occupied consumer passed scoped checks, including a nonzero two-odd coefficient Hom; fresh publication repeat and full integration remain separate gates. |
| Global probe adjunction and dot | [ef53181050](https://github.com/apellis/odd-lean/commit/ef53181050a914dcfb682c996412ae41326e85c0) (`OddMath/QuiverHecke/CyclotomicAction/ELVProbeWeightAdjunction.lean`) | Both global right-adjunction and signed-dot producer/consumer pairs passed scoped checks; whole weight dot-unit and complete probe-family assembly remain open. |
| Local pre-adjunction preparation | [e661ef0b68](https://github.com/apellis/odd-lean/commit/e661ef0b682ae0876cbc60cdd4a038c65bd4df4c) (`OddMath/QuiverHecke/CyclotomicAction/ELVProbeVacuumPreAdjunction.lean`) | Private zero-lower braid and height-transport helpers checked; actual adjacent-record specialization and paired consumer remain pending. |

## Dependency order and readiness

| Target | Ready to start? | Established inputs | Completion criterion / blocker |
| --- | --- | --- | --- |
| Fixed-content/weight matrix inverse assembly | Constructed in strict paired checks | Prescribed principal/unit/cap squares, supported and absent inverses, whole input-natural product assembly | Full integration gate pending; use the chosen maps in the factor |
| Reservoir factor family | Constructed in fresh strict paired checks | `elvRouquierFamily`, both local inverse families and all seven `elvRouquierMulticolour` fields with original Sc | Full CI verified in #1014; use the selected factor in the swapped assembly |
| Global probe family | In progress | Evaluated old subcategory, E/F/parity/product closure, entire natural dot inverse, old quotient square/slides and matrix inverses | Chosen whole-weight right adjunction and signed dot are full-CI verified in #1011; whole-dot inverse and equal crossing pass strict paired checks; finish signed slides, braid, local records and multicolour transport |
| Concrete swapped action | Factor interfaces available; instantiation incomplete | Ordinary and transposed blockwise denominator units, generic braid/inverse assembly | Supply complete probe/reservoir factors and chosen mixed inverses/coefficients; prove the literal central augmented-matrix squares and residual closure memberships |
| Vacuum and bubble recovery | Operator comparisons available; action attachment incomplete | Tensor-vacuum whole-module chart, prescribed cap polynomial identities, word/coefficient charts and joint source detection | Identify full chosen-action bubble/corner operators on every vector and construct observations |
| Vacuum path collapse | Full build, global axiom audit and all non-vacuity checks verified in #1010 | `SPath.subsingleton_of_upward_probe_zero`, `sum_of_upward_probe_zero` and the constructed `reservoirPath` for every upward labelled word | The even whole-functor identification with reservoir postcomposition passed full CI in #1014 in `ReservoirWordFunctor`; attach the selected vacuum value and contextual dot/crossing operators before constructing an observation |
| Final Phase 1 nondegeneracy | Blocked on concrete observations | Finite-colour reduction, upward/oriented equivalence, observation consumer and proved ground-ring descent | Supply observations for every required bound/word/weight for symmetrizable homogeneous data; inhomogeneous parameters belong to Phase 2 and nonsymmetrizable data are excluded |

## Prescribed matrix and coefficient-row successors

The #988 source head `1f62b66a` passed the full warning-free build, global
axiom audit and every concrete consumer (run 41581218832), and is integrated
at `393fca27`. Its native RouquierData has the same-colour square field;
its all-block quadratic component identity is also verified. The remaining
native mixed/braid/slide and local-inverse fields are not supplied by that
bundle.

The next strict locally checked integration supplies relative-content
finite matrix maps and both input-natural inverses, weighted fixed-output
module inverses natural in global-truncated inputs, and both scalar
prescribed forward identifications including the ordinary absent-colour
unit boundary. Changing-content mate and matrix-entry supernaturality is
retained. Complete canonical-content and original-weight endpoint/field
transport remains necessary; use the selected full source/target charts.
The canonical-content diagonal mate square now passes through those charts
with its actual parity square. Attach its unit/dot and dot/counit fields
before invoking the finite inverses for the chosen action.

The signed source composition and chosen scheduled content/original-weight
induction components are locally checked. The rectangular crossing is
identified with its chosen content word counterpart. Complete chosen
weight-action generator evaluation and relation-preserving factor assembly
before using the source coordinate kernel as action faithfulness.

The actual full-old probe extraction row has its signed polynomial and
parity. The inverse-unit rows are now homogeneous content module maps,
surjective on every component and equal to the prescribed module unit
coefficient at empty output. Scalar inverse coefficient transport retains
the canonical unshift and every row index. The next risk target is to
identify their old-field/module-map specialization through the selected
FE chart, then derive the normalized left-cap window and mixed slide.
The ordinary right counit comparison does not discharge this obligation.

These successor sources passed the full warning-free build, global axiom
audit and every concrete consumer in #989 at source head `7ac6e4f9`
(run 41585699842), integrated at `d73f2f2f`. All 40 producers and 75 exact
producer/consumer blobs also passed strict local and combined-import checks.
Exact module scope is in STATUS and the mathematical topic notes.

The next locally checked sources supply both native multicolour quadratic
fields, whole chosen weight-dot evaluation, every canonical-content unit-dot
power through the selected full charts, exact scalar old inverse-row field
binding, supported chosen weight unit/counit squares and even flattened
weight-triple coordinates. Their full warning-free build, global axiom audit and every consumer passed in #991 at source head `c18b8721` (run 41588533754), integrated at `ea35e5ba`. Next attach
the native coefficient cap to its exact scalar inverse-row field and derive
the normalized probe window. The whole original-weight distinct mate inverse
and its parity now pass strict paired checks, including both round trips and
odd-input naturality; the selected native coefficient cap has its prescribed
degree and a nonzero regular-probe value. Prove the native slide/braid fields,
original-weight same-colour local inversions and canonical diagonal cap-row
and inverse fields. The chosen crossing
evaluation and final observation recovery remain separate obligations.

## Phase 1 field endpoint and Phase 2 boundary

The current field construction retains `sy : Symmetrizer D` and homogeneous
parameters. With that fixed datum it must furnish `CharZeroFieldNondegeneracy D`;
the existing ground-ring theorem then supplies ordinary rings with 2 invertible.
Homogeneity is relaxed only in Phase 2; symmetrizability is retained in both
phases. For Phase 2, specify the graded-coefficient/inhomogeneous parameter
presentation, prove the required extension and scalar comparisons, and check
the all-even specialization against the cited even benchmark. No proof route
for nonsymmetrizable data is to be developed. See
[FieldScopeBoundary](FieldScopeBoundary.md).

## Native probe normalization and remaining action fields

The native left-cap field, all-row Kronecker window, SAME-dot signed probe
polynomial, canonical counit/all cap rows, weight mate boundary, triple
coherence and selected append-unit/cyclicity batches passed full CI in #993
at `f0a2ed23` (run 41594069793). These are established dependencies.

The #995 integration passed the full warning-free build, global axiom audit
and all consumers at `a51a6f9a` (run 41605147758), integrated at `8f9ad250`.
It proves the prescribed same-colour
slides and braid and both distinct-colour slides on original weights, on all
modules and outputs. It also identifies normalized crossing/mate maps and
all native unit/cap powers with the old grid operators. Mixed-colour braid
assembly remains open.

Generic finite coordinate inverses now produce both local inversion structures,
with exact given forward maps and homogeneous entries; the old grid isomorphisms
supply constructed examples. All six canonical content chart isomorphisms are
even in both directions and have exact total-component formulas. Transfer the
given weighted local inverses through these charts, including the absent
predecessor with zero EF but retained FE, then assemble input-supernatural
inverse-entry families and the original-weight local inversion fields.

The selected cap family is input-supernatural. Its native module window and
literal pre-Hom cap are checked; shifted coordinate dot and raw pre-E dot
differ by the proved Koszul factor, also at every power. The weighted inverse
row has its actual homogeneous coefficient map, literal power-reservoir cap
comparison and full A/T superlinearity, including nonzero odd products.
The remaining obligations are concrete adjunction/factor assembly and the
prescribed mixed slide and bubble operators. The generic adjacent Rouquier
left-adjunction construction already exists in `RouquierFTriangle`; constructing
its concrete local inputs remains necessary.

The subsequent checked component inverses now include both `weightedContentLocalInverseFrom`
and `weightedContentLocalInverseTo` with the prescribed forwards. Every canonical
unit column and cap row has its whole chart square, and the absent-predecessor
canonical inverse is constructed. The supported principal square and concrete input-family assembly remain
open. `AugmentedInverseNaturality` now supplies both automatic inverse-entry
family constructors from the given forward families and pointwise inverses,
including canonical zero extension outside the finite window.
`ELVGridLocalInverseFamilies` bundles both given grid inversion families,
with the constructed old matrix natural isomorphisms as concrete inputs.
Use these families to construct the prescribed adjacent old local records. All three positioned-dot comparisons and both adjacent crossing comparisons
now pass through the same chosen triple chart. Attach the original-Sc
correction polynomial to those operators.

The existing adjacent-left-adjunction constructor is packaged with only two
local records and the required square-zero/braid equations. Its regular-probe
raw row is determined by the actual unit-column window; the native normalized
counit and output-shifted pre-Hom signs cancel. Scalar-evaluation uniqueness
extends to the occupied F(E T0), without assuming evaluation at T0 is faithful
on every module. Construct the old-category empty and one-colour local records
using the existing old grid natural isomorphisms, then apply that constructor.
The given weighted unit and dot now satisfy the cap Kronecker window as
whole content-zero module maps, also for the polynomial low window. These
are the literal operators required by `InverseCapMoments`.
Actual weighted all-power moments and χ/δ series hold on every coefficient
vector. The polynomial module cap λ·(D²+1)^M has all closure formulas,
including nonpositive first closure and a second closure distinguishing
χ₁+2 from χ₁−2 on nonzero odd input. The prescribed swapped mixed inverse
and bubble identification remain.

Chosen append-unit calculation and full-coefficient cyclicity are established;
finish the chosen whole crossing equality and final observation recovery.
The local-inverse, triple-component and probe-adjunction integration #997
passed all full-package gates at `679df033` (run 41607159909), integrated at
`ce03b2b1`. Automatic inverse naturality, three triple-dot squares, literal weighted
cap windows and grid inverse families passed full CI in #999 at `90c42b0b`
(run 41610482426), integrated at `d02c6561`.

## Chosen word evaluation and absent local families

The chosen content and original-weight word-module crossing squares now
hold for every full coefficient vector, including absent components; their
occupied paired consumers retain a nonzero product of two odd coefficients.
Finish append/context coherence before the final observation/recovery step.

Actual absent-content and absent-weight input inverse families are constructed
from the given forward maps; arbitrary heterogeneous product assembly retains
the actual common height counts. The supported canonical principal square
and its concrete block transport remain the central missing case.

For the old probe, conjugating the existing missing-colour unit matrix through
the chosen FE/value charts gives the exact unit-column matrix and its even
module isomorphism for every old input, without scalar-evaluation hypotheses.
Use its inverse rows and automatic naturality to construct the empty local
record; the old grid natural isomorphisms and exact Rouquier-mate/grid equality
supply the one-colour record. The earlier all-input identification with a
preselected normalized cap is not a prerequisite: the checked row uniqueness
at the regular probe and F(E T0) supplies the evaluations actually used.

The local pre-Hom adjunction now comes from the existing two-adjacent-local
constructor with its prescribed unit and counit; both Koszul signs cancel
in the evaluated counit. Its local records remain explicit intermediate
inputs. The evaluated mixed bend must still be compared with the prescribed
central entry, retaining the raw pre-dot and inverse-power signs.
These thirteen producers passed full CI in #1001 at `84340134`
(run 41615387064), integrated at `daffec02`.

## Factor families and evaluated-cap successors

The supported canonical principal square, supported content/weight inverses
and whole input-natural weight inverse families pass strict paired checks.
`elvWeightRouquierLocal_nonempty` supplies the actual local records with
exact cutoff/highest-weight compatibility. `elvRouquierFamily` now assembles
the prescribed E/F, adjunction, signed dots, crossings, square, same-colour
braid and these constructed local records on the original weight group.
No inverse, compatibility or factor-action premise remains in this family.

Both corrected and uncorrected native braid fields are checked on every
input/output sector; the general consumer includes three distinct odd
colours with nonzero pair Cartan entries. The exact presentation sideways
crossing is identified with the constructed rectangular inverse. Assemble
these fields with the established quadratic/slide relations into the complete
multicolour structure, then connect the full factor to the swapped action.

The evaluated old probe category is closed under prescribed E/F, parity and
arbitrary products. Its entire signed induction dot has a constructed
natural inverse, with the correct odd parity. The checked successors now
supply canonical content reindexing, stored-target append/restriction,
their actual balanced adjunction, their whole signed-dot inverse and
original-weight E/F with genuine zero modules at absent predecessors.
Complete the whole weight adjunction, dot unit, crossing and local inverse
transport to construct the probe family; retain the same unit, cap and dot. The generic
ProbeReservoir interface accepts these factors directly; the older ordinary
polynomial-specific global constructor is not an additional requirement.
Do not assert a dot unit on arbitrary old modules.

The old empty-content local record and its regular/F(E(T0)) cap bindings
are constructed. The remaining adjacent one-letter record needs literal
old slide transport through the checked induction-composition chart; the
given negative crossing square is checked. Then instantiate the existing
adjacent-local left-adjunction constructor, retaining both prescribed Koszul
factors and the raw shifted pre-dot.

Even word charts, native contextual dots/crossings and full-A/T coefficient
insertions are checked. The latter retain inhomogeneous arrows and the minus
on reversing two odd insertions. Finish chosen Hom-action evaluation before
using the established quotient/source windows as faithfulness.

The tensor-vacuum module chart, prescribed inverse cap, negative-height
polynomial annihilation and equal-level normalization use the same actual
operators and have occupied odd consumers. Identify the chosen full swapped
augmented inverse and its bubble/corner operators, then supply all-vector
observations to the existing recovery theorem.

PR #1003 passed its full build, axiom audit and all consumers at `72aa0c1c`
(run 41625277102), integrated at `41673fa3`. PR #1005 passed the same gates
at `a85d1660` (run 41626194575), integrated at `5695663e`.
PR #1006 passed the full build, axiom audit and every consumer at
`804dd66d` (run 41628541714), integrated at `e4374193`. The six probe
successors passed the same gates in #1007 at `0034b2d8`
(run 41630889345), integrated at `d783c565`; their checked source prefix
is `04e78b61`, with 12 source/consumer blobs and 214 owned-declaration audits.
Phase 1 ground-ring descent is already formalized; the separate Phase 2
parameter extension and the exclusion of nonsymmetrizable data remain explicit.

## Current comparison interfaces

The ten coefficient-power/comparison producers integrated in #973 passed the
full build, global axiom audit and all consumers at source head `911f3e12`
([CI](https://github.com/apellis/odd-lean/actions/runs/41546394528)). The
literal T-annihilated category, numerical ideal sandwich, content dots and
scalar ordinary counit are established inputs.

The generator-comparison integration #976 passed its full build, global
axiom audit and all consumers at source head `861aeadd`
([CI](https://github.com/apellis/odd-lean/actions/runs/41550563550)). It supplies:

* actual A/T algebra presentation and bounded coefficient detection, parity and
  regular left coefficient module, retaining nonzero independent odd vectors;
* chosen content ordinary cup/cap squares and EF/FE all-map natural charts;
* six-category grid and scalar selected iterated/conjugated-transform formulas;
  selected weighted iterated induction and its prescribed signed crossing;
* ordinary-right mixed coefficient-kernel isomorphism and explicit tensor
  realization, retaining exterior first-factor twists and no flatness premise;
* full homogeneous half-turn composition, literal first/last-boundary quotient
  equivalence and bounded injection of x mapped to [htCoef x] with the written
  reservoir schedule. The seven earlier contextual reversal/ideal producers and
  all 332 owned declarations were rechecked; these are prior source results.

The actual arbitrary-module distinct forward identity and bundled homogeneous
input-natural inverse passed full CI in #977.
Content signed crossing/mate and finite parity/product attachment, category-
changing scalar/weighted ordinary mate squares are scoped-checked below;
normalized cap rows and complete matrix transport remain next. The
literal old T-vacuum and contentwise induction-dot nilpotence are now
scoped-checked. Actual word-value/Hom coordinate evaluation and normalized
swapped bubble attachment remain open.
See [HalfTurnHomogeneous](HalfTurnHomogeneous.md),
[HalfTurnBoundedDetection](HalfTurnBoundedDetection.md),
[CoefficientPowerQuotient](CoefficientPowerQuotient.md),
[CoefficientPowerGrading](CoefficientPowerGrading.md),
[ContentEFComparisons](ContentEFComparisons.md) and
[DistinctMateKernel](DistinctMateKernel.md).

## Vacuum and mate attachments now available

The interfaces integrated in #977 passed full build, global axiom audit
and every consumer at source head `61f93b2e`
([CI](https://github.com/apellis/odd-lean/actions/runs/41554732093)). They give the distinct
rectangular mate a bundled homogeneous inverse on all old modules, natural in
arbitrary input-module maps. Its forward map is exactly the given mate and
both inverse directions have parity p(i)p(j); transport to the chosen content
and original-weight functors remains to be completed.

The literal old T-vacuum is now constructed by balanced extension along the
fully faithful empty coefficient embedding (object-only universe lift).
Its chosen empty component is evenly A/T, nonempty formal contents vanish,
and every element of T acts by zero. Both independent odd coefficient vectors
survive. Prescribed unit-inverse rows give the actual extraction window and
coefficient sign law. The original signed induction dot has a positive
contentwise exponent on every T-annihilated module, through the existing
weighted nilpotence bound and the chosen dot comparison. Finite module
dimension and a common weight-fibre exponent are not assumed.

The source coefficient/cyclotomic quotient and literal scalar-power Hom spans
now have exact kernel/image/preimage comparisons with the existing old Homs.
The half-turn maps directly into those reversed/twisted OldCategory Homs,
retains total-parity composition and the prescribed bounded reservoir schedule.
Actual iterated regular A/T vacuum word values and their precise transformed
coordinate kernels are scoped-checked below. The signed old-module Hom/Yoneda chart, native maps and selected dot
comparison are scoped-checked below. Attach the pair crossing and the chosen
swapped Hom-action evaluation on every coefficient vector; no action-faithfulness premise is permitted.

See [DistinctModuleIso](DistinctModuleIso.md),
[CoefficientPowerVacuum](CoefficientPowerVacuum.md),
[CoefficientPowerRows](CoefficientPowerRows.md),
[CoefficientPowerNilpotence](CoefficientPowerNilpotence.md),
[SourceQuotientComparison](ELVSourceQuotientComparison.md),
[SourcePowerComparison](ELVSourcePowerComparison.md) and
[HalfTurnOldQuotient](HalfTurnOldQuotient.md).

## Higher moments and matrix chart inputs

The actual regular A/T vacuum now has scoped-checked higher moments,
including the ordered recurrence and full coefficient parity law. Its
normalized remainder series is the two-sided formal inverse of the reversed
literal monic polynomial over A/T. The all-height signed moment is exactly
the triangular sign times that remainder coefficient. Both independent odd
colours retain a nonzero −[δ_i] second signed moment. The closed χ/δ values at the unit are now scoped-checked below;
arbitrary-vector moment and coefficient operators are now scoped-checked
below. Identification with the prescribed swapped caps/bubbles remains open; these series alone do not supply an action or recovery identity.

Selected weighted source/target charts are now genuine linear equivalences
with the prescribed forward maps. The selected scalar comparison transports
mapped dots and all powers, and the generic power comparison retains the
whole output parity involution. Next compare the actual normalized cap/unit
matrix entries through these charts and transfer the proved inverses.
See [CoefficientPowerMoments](CoefficientPowerMoments.md),
[CoefficientPowerRemainders](CoefficientPowerRemainders.md),
[WeightedMatrixCharts](WeightedMatrixCharts.md),
[OperatorPowerComparison](OperatorPowerComparison.md) and
[ProbeDottedComparison](ProbeDottedComparison.md). These inputs passed full
CI through #982; the newer finite-family successors below await integration.

Recovery is required separately for each original weight, word pair and
degree bound: `SwappedVacuumEvaluation` and `SwappedVacuumObservation`
already have those indices. Choose a sufficiently large scheduled reservoir
for each requested window. No interface change or extension to every small
cutoff is needed. Construct the actual action and its all-affine coordinate
identity on that window; a stronger all-word fixed-cutoff family is optional.

## Word coordinates and closed odd moments

`powerWordModule` is actual balanced induction of the regular A/T module
along coefficient insertion at each old word. Its empty value is the chosen
vacuum, and `powerWordAppendIso` uses the selected induction-composition
comparison. The generator h tensor 1 is onto; its kernel is exactly the
independently defined two-sided elementary-power image, using the original
coefficient order and no flatness. The actual word values belong to the
literal T-annihilated category. Composing with the signed half-turn gives
the transformed-ideal kernel and the prescribed bounded reservoir schedule.
The consumer retains both independent odd exterior generators at an occupied
two-strand word value. Both producers and the consumer are scoped-checked,
with 69 owned declarations audited; full CI verified through #982.

The enriched old-module Yoneda formula now descends through this proved
generator kernel, retaining the parity of the complete old coefficient arrow,
including the external A/T factor, and the chronological composition sign.
Native maps agree with the existing balanced induction transformations, and
the selected append comparison intertwines the actual dot on all vectors.
Next attach the recursive selected pair crossing and the chosen swapped
Hom-word functors to these coordinates.
The source-coordinate kernel theorem does not itself prove action evaluation.
See [ELVPowerWordCoordinates](ELVPowerWordCoordinates.md) and
[PowerWordHalfTurnCoordinates](PowerWordHalfTurnCoordinates.md).

The complete odd series now has scoped-checked values at the actual unit:
even moments are the coefficients of 1/C(−z), and odd moments are
(−1)^(N+1)δ times those coefficients. The occupied consumer checks positive
cutoffs of both parities, with nonzero δ, χ_1 and δχ_1. The moment-map operator identities on arbitrary A/T vectors are now
scoped-checked, as are the genuine native coefficient module actions and
their induction/restriction comparison. Next attach the prescribed signed
probe polynomial and the actual swapped caps/bubbles. See
[CoefficientPowerOddSeries](CoefficientPowerOddSeries.md).

The ordered changing-category mate now has its prescribed homogeneous
degree proved from the given crossing and even adjunction maps, without
an inverse premise. The actual original-weight pair dots also agree with
independent single-letter content dots under the selected canonical pair
equality. Their paired consumers are scoped-checked, with 3 and 9 owned
declarations audited respectively; full CI verified through #982. Finish the content
matrix attachment and assemble the weight crossing-square and triple
relations. See [InductionGridMateParity](InductionGridMateParity.md) and
[WeightPairDots](WeightPairDots.md).

## Selected matrix entries and native word maps

The old-content self-colour mate tensor square is scoped-checked on the
unweighted, untruncated OldContentCategory module categories, through the
chosen EF source and restriction target charts. The distinct-colour positive
mate has a pointwise raw coend inverse there for every input module. The
whole self-colour module square and prescribed finite inverse attachment
remain next. Homogeneous old-content/global-truncated distinct inverse
bundles, finite coordinates and canonical ContentModules E/F charts are
scoped-checked below; canonical-content inverse and original-weight
assembly remain separate. Neither result assumes a mate inverse or flatness.
See [ContentAppendMate](ContentAppendMate.md) and
[ContentDistinctMate](ContentDistinctMate.md).

The selected weighted charts intertwine every prescribed unit/dot column
and dot/counit row. Scalar transport also retains every canonical shifted
cap target through an even parity/restriction isomorphism, natural on odd
and inhomogeneous input maps. Its cap slots bind literally to the old finite
cap-matrix fields; the original whole-output parity correction is retained.
Next attach the unit source coordinates and finite inverse products using
these same entries. See [WeightedMatrixRows](WeightedMatrixRows.md),
[ProbeCapRowComparison](ProbeCapRowComparison.md),
[ParityRestrictionComparison](ParityRestrictionComparison.md) and
[ProbeShiftedCapComparison](ProbeShiftedCapComparison.md).

The actual power-word module Hom chart is now a signed linear equivalence.
Its native arrow maps have the full coefficient twist, signed composition
and equality with the established induction transformation. The selected
append comparison has its literal tensor formula and intertwines the
actual dot on every vector. Finish the recursive selected two-append
crossing with its equal-colour minus, then the chosen swapped Hom evaluation.
See [PowerWordYoneda](PowerWordYoneda.md),
[PowerWordMorphisms](PowerWordMorphisms.md) and
[PowerWordAppendDot](PowerWordAppendDot.md).

The inverse-row moment map on arbitrary A/T vectors is exactly left
multiplication by its proved moment. Genuine coefficient module maps retain
the original algebra order, descend literally to A/T and commute with append
induction/restriction. The signed probe annihilator on the actual vacuum block is scoped-checked
below. Attach the mixed inverse cap and source-placed bubbles.
See [CoefficientPowerMomentMaps](CoefficientPowerMomentMaps.md),
[CoefficientModuleMaps](CoefficientModuleMaps.md) and
[CoefficientAppendMaps](CoefficientAppendMaps.md).

The actual weight crossing's pointwise linear formula and two-crossing
composition now use the selected source/target comparisons, including
supported and absent-double-predecessor cases. Next attach the original-Sc
polynomial in the independently defined weight dots and assemble the triple
relation fields. See [WeightPairCrossingTotals](WeightPairCrossingTotals.md).
These inputs passed full CI through #982 at `5d918b82`
([build and audits](https://github.com/apellis/odd-lean/actions/runs/41568326406)).
They do not construct the complete factor or swapped action.

## Finite matrices, canonical truncated contents and probe attachment

The following finite-family, truncated-content and probe inputs passed
full build, global axiom audit and every consumer in #984 at `bf22957c`
([CI](https://github.com/apellis/odd-lean/actions/runs/41572490013)).
The weight-coordinate and cap-attachment inputs also passed full build,
global axiom audit and every consumer in #986 at `4279a451`
([CI](https://github.com/apellis/odd-lean/actions/runs/41575246618)).
The newer successors below are scoped-checked until their own gate completes.

The old-content and global-truncated distinct rectangular mates now have
homogeneous module and input-natural inverses with exactly the prescribed
forward maps. They require no additional inverse or flatness hypothesis.
The canonical coefficient-truncated content inclusion is fully faithful;
supported extension has its selected counit isomorphism, and the chosen
E/F charts have literal all-coefficient tensor formulas. Next transfer the
global truncated distinct inverse through these exact content charts, then
to the original weight products. See [TruncatedDistinctIso](TruncatedDistinctIso.md)
and [ContentBlockAppend](ContentBlockAppend.md).

The prescribed grid and weighted finite components now have their exact
shifted mate/unit/cap entries. Genuine scalar E/F, F/E and value charts
assemble into whole even finite-family equivalences. Every scalar entry
and both whole finite matrix comparison squares now hold with no additional
compatibility premise. Transport the prescribed old inverses through these
same squares. The weighted all-vector mate and all-power unit/cap squares now hold, and
finite parity products conjugate the given old matrix isomorphisms to the
weighted spaces. Identify their forward maps with the independently
prescribed weighted finite components before asserting those components
are invertible. The old-content
versions give genuine finite coordinates at explicit predecessor content
i::ν. Finish the whole prescribed matrix comparison and transport the
existing old matrix inverses. The absent-predecessor case must be proved
separately or encoded with an actual predecessor fibre; it cannot be
replaced silently by i::ν. See [InductionGridMatrixFamilies](InductionGridMatrixFamilies.md),
[ProbeMatrixFamilyCharts](ProbeMatrixFamilyCharts.md),
[ProbeFiniteMatrixComparison](ProbeFiniteMatrixComparison.md),
[ContentGridMatrixCoordinates](ContentGridMatrixCoordinates.md) and
[WeightedMatrixComponents](WeightedMatrixComponents.md) and
[WeightedMatrixInverse](WeightedMatrixInverse.md).

The actual empty-source one-letter probe vacuum satisfies (D²+1)^m=0
for odd D, on the whole induced module and its supernatural-Hom
precomposition action, both before and after scalar comparison. Its
selected old and ordinary append-unit vectors are nonzero at every
positive level; at level one D²v=−v. This settles the vacuum-block
polynomial input and its occupation. It supplies neither the concrete
mixed slide nor the final chosen swapped cap/bubble. Attach those exact
maps and their source placements before claiming recovery; no identical
last-dot exponent is asserted on arbitrary contents. See
[ProbeVacuumPolynomial](ProbeVacuumPolynomial.md),
[ProbeOldVacuumPolynomial](ProbeOldVacuumPolynomial.md) and
[ProbeVacuumUnit](ProbeVacuumUnit.md).

## Weight coordinates and polynomial cap attachment

The two actual supported weight crossings give the original-Sc operator
polynomial at the actual output content under the selected pair chart.
Both independently defined weight dots now intertwine through exactly
that same chart, retaining the actual intermediate block. The complete
component squares and their all-vector equations are scoped-checked.
The positioned polynomial and absent-predecessor branch are now scoped-checked
on every component; same-colour square zero also holds as a native
two-morphism. Assemble the native mixed polynomial, braid and slides;
no complete local inverse or RouquierFamily is yet claimed.
See [WeightPairQuadratic](WeightPairQuadratic.md) and
[WeightPairDotCoordinates](WeightPairDotCoordinates.md).

All-power old-content cap rows are scoped-checked through the genuine
selected E/F and inclusion-value charts, with no evenness, compatibility
or invertibility premise. Together with the unit columns they supply both
dotted sides of the relative-content finite matrix. Finish its whole mate
square and finite assembly, then attach the given global old inverses
through those exact fields. Retain the explicit i::ν predecessor scope;
empty output and absent-i contents need their own branch. See
[ContentMatrixCaps](ContentMatrixCaps.md).

The actual polynomial functional λ(D²+1)^M on the power vacuum has its
first normalized closure on every coefficient vector: for N≥2M and N>0,
λ(D²+1)^M D^(N−2M)u=L_((-1)^(N+1)δ). The occupied two-odd consumers
retain the original left multiplication order at zero and negative height.
This computes the candidate, rather than identifying the prescribed mixed
cap. Construct the actual probe extraction row and chosen mixed maps,
prove their slide and normalization, and only then use the existing
principal/negative-cap recovery theorem to attach the candidate and the
source-placed bubbles. See [CoefficientPowerPolynomialCap](CoefficientPowerPolynomialCap.md)
and [CoefficientPowerNonpositiveCap](CoefficientPowerNonpositiveCap.md).

## Prescribed inverses and chosen evaluation attachment

The following successors pass strict scoped producer/consumer checks and
owned-declaration axiom audits; their full integration CI is pending.

The canonical truncated-content distinct mate is now an isomorphism of
modules and of its whole input-natural family, with exactly the prescribed
positive forward map and inverse degree p(i)p(j). Transport it through the
actual weight adjunction/crossing components and prove the absent-colour
sectors before asserting the original-weight inverse. See
[ContentBlockDistinctMate](ContentBlockDistinctMate.md).

Both complete prescribed weighted finite matrix squares now hold, and the
actual forward components have explicit even inverses at their exact
nonnegative/nonpositive heights. Both inverse identities use the given
forward maps. Restrict to fixed output content to bundle module inverses,
then prove input-module supernaturality. The whole old-content mate square
also now holds on every coend vector, completing its three unshifted field
comparisons; its shifted finite entry assembly remains separate. See
[WeightedMatrixComponentInverse](WeightedMatrixComponentInverse.md) and
[ContentMatrixMate](ContentMatrixMate.md).

The scalar conjugated inverse candidates retain the given global old
inverse. Their i-present prescribed forward identification is still open.
At absent-i output, including genuine empty output, the old global EF
source and principal slot are proved zero, height is nonnegative, and the
given old unit inverse drops to exactly the remaining unit/dot columns.
Finish the ordinary upper-F/E and value/column transport of that branch;
do not confuse empty output with an empty predecessor. See
[ProbeMatrixInverseCandidates](ProbeMatrixInverseCandidates.md) and
[MissingColourMatrix](MissingColourMatrix.md).

The independently chosen equal and distinct word crossings now agree
with full-coefficient fromArrow under the recursive selected comparisons,
including the equal-colour minus. Selected append and every right suffix
intertwine arbitrary inhomogeneous old arrows. These are actual module-map
identities. Next prove the signed source composition/U cancellation and
attach the chosen upward evaluation through the scheduled old-to-truncated
and content/weight charts. Source-coordinate kernels alone are not action
faithfulness. See [PowerWordPairCrossing](PowerWordPairCrossing.md),
[PowerWordDistinctCrossing](PowerWordDistinctCrossing.md) and
[PowerWordContexts](PowerWordContexts.md).

The original-Sc quadratic holds in the independent weight dots on all
components, supported or absent. The actual PiSCat generator bundle
`elvRouquierData` has its native same-colour square equation and retains
the chosen right adjunction. Complete the native mixed relation, braid,
slides and local inverse fields before constructing RouquierFamily. See
[WeightQuadraticComponents](WeightQuadraticComponents.md) and
[ELVRouquierData](ELVRouquierData.md).

The probe's literal ground coordinate and full-old ground-valued last
inverse row now have occupied consumers and exact all-scalar dot windows.
Attach its intrinsic parity, the selected native coordinates and the
normalization of the prescribed left cap. The actual mixed slide and
source-placed bubble identification remain open. See
[ProbeVacuumCoordinates](ProbeVacuumCoordinates.md) and
[ProbeExtensionRows](ProbeExtensionRows.md).

## Categorical inverse: precise interfaces

Read [DeformedCyclotomicTopRow](DeformedCyclotomicTopRow.md),
[DeformedMackeyBoundary](DeformedMackeyBoundary.md),
[DeformedBoundaryDivision](DeformedBoundaryDivision.md),
[DeformedRouquierMatrix](DeformedRouquierMatrix.md) and
[DeformedMatrixComparison](DeformedMatrixComparison.md).

Use the independently defined balanced source, alpha, pprime, short crossing
and quotient maps. The arbitrary-Hom raw inverse and its actual categorical
attachment are now verified for both height signs and both moving parities
(#828/#889). The actual first row is the ordered crossing mate; the other
entries are the literal ordinary unit/dotted cap maps in the prescribed
parity-shifted coordinates. For even moving colours, canonical J uses
coefficient(0) and every cap row has the constant negative ordinary
normalization (#862). Retain the printed odd profiles and the separate
self-colour leading unit. Their arbitrary-module component transfer is now
verified in #951/#952; fixed-content/weight functor assembly remains separate.

### Arbitrary-module kernel transfer

The generic coefficient-kernel tensor isomorphism and finite kernel
products are verified (#878/#890). The actual ordinary-right kernel
matrices, source-right covariance, Hom/IndRes/finite-family quotient
coordinates, and both whole arbitrary-module forward-map identities are
full-CI verified and integrated through #932 (#911/#915/#916/#921/#923).
Their consumers retain
cofinally nonzero full exterior-coefficient inputs, with both moving
parities and zero finite counts. The actual finite SVec maps and their
evenness for every input module are full-CI verified and integrated through
#932, retaining the exact #896 producers.

Canonical kernel/source and finite-family coordinates, with bundled mate-row
equality, are full-CI verified in #950. `ELVKernelMatrixBijective` (#951)
compares both moving parities and height signs to the prescribed representable
matrices at literal word endpoints. Abstract parity elimination keeps the
coefficient maps folded during subtype conversion.

The target count is fixed by content height Q−S (#900/#903). Matching-content
bijectivity combines with the off-content zero-component matrices (#914/#928)
to give `actualPositiveKernelMap_bijective` and
`actualNegativeKernelMap_bijective` on every old source at that count.

`ELVModuleMatrixInverse` (#952) tensors these coefficient isomorphisms with
every old supermodule. `moduleUnitMatrixIso` and `moduleCapMatrixIso` have
exactly the prescribed unit/cap matrices as their forward maps, for both
height signs and moving parities, including empty finite families. Their
forward parity (#896) implies inverse parity; no arbitrary-kernel evenness
or flatness premise is introduced. The concrete mixed-data consumer checks
both inverse products on representables and audits all owned declarations.
See [ModuleMatrixInverse](ModuleMatrixInverse.md).

`ELVContentMatrixInverse` supplies full-CI verified natural isomorphisms for
the restrictions of the old-category matrices to fixed output content.
Its `contentUnitMatrixIso` and `contentCapMatrixIso` are even supermodule
isomorphisms, with literal component identities and inverse naturality along
arbitrary output arrows. The paired mixed consumer and axiom audit pass
locally and in the integrated full CI for #953/#954. This does not yet identify these restricted
modules with the chosen content E/F composites.
`ELVMatrixEntryNaturality` now gives full-CI verified input-module naturality
of every literal shifted unit/cap entry. Its dot-power, unit, cap and mate
families retain their supernatural parity before shifting. The paired
mixed representable consumer and owned-axiom audit pass locally and in
[full CI](https://github.com/apellis/odd-lean/actions/runs/41489136665).

`ELVMatrixFunctorNaturality` now assembles these summand maps into the
finite-family source/target functors and whole unit/cap natural transformations
in the input module. Both functors are additive, linear and parity preserving.
`ELVContentMatrixFunctorInverse` provides `contentUnitMatrixFunctorNatIso`
and `contentCapMatrixFunctorNatIso`, combining this naturality with the existing
output-content component inverses. They are natural along every input-module
map and retain literal forward components and even inverses, including both
height signs/parities and zero finite counts. Strict scoped producer and
paired-consumer checks and all 64 owned-declaration axiom checks passed
[full CI](https://github.com/apellis/odd-lean/actions/runs/41532403900)
at source head `55c6d763`, integrated in #961. See [MatrixFunctorNaturality](MatrixFunctorNaturality.md).

The chosen EF/FE charts and ordinary cup/cap comparison are now scoped-checked.
Finish signed crossing/mate and finite parity/product compatibility, then
transfer the literal matrix inverses to original-weight functors. Keep the target-fixed count,
chosen source parity coordinates and literal ordinary unit/cap entries.
Prove compatibility with the selected dot, crossing and adjunction maps
before using these inverses in a full-ELV factor action. These old-category
natural isomorphisms alone do not supply that action.

`equalCrossComponent_braid` in `ELVOldAppendBraid` (in the
`ELVOld.CyclotomicCrossingTensor` namespace) supplies the untruncated
coefficient braid for the actual prefix and suffix equal crossings. Its
producer, concrete representable consumer and both owned audits pass
strict scoped checks, with full CI verified in #1011. `oldTripleCross_braid` in `ELVOldInductionBraid` proves
the subsequent whole-map braid on direct triple induction, with its
superopposite signs; its producer, occupied consumer and all 15 owned
audits also pass, with full CI verified in #1011. The shared signed
argument is now exposed in `ELVModuleInductionBraid` for the changing
content grid; the extraction and unchanged OLD consumer pass fresh strict
checks, with one plus fourteen owned audits, and full CI in #1014. `ELVOldNestedBraid` now
identifies both chosen negative prefix/suffix crossings through the same
canonical triple flattening and proves their braid on every old module.
Its producer and concrete consumer pass strict checks; the shared-grid
refactor retains the same statements and audits all sixteen remaining
owned declarations. The original twenty-declaration form passed full CI
in #1014; the shared-grid refactor awaits integration. Restriction to evaluated fixed contents and weight transport
remain; these results do not yet prove the probe weight braid.
See [OldNestedBraid](OldNestedBraid.md).
`ELVInductionGridBraid` and `ELVOldContentBraid` now supply the same
comparison on four consecutive content categories and the prescribed
negative braid on every old content module. Both producers and the
mixed/shifted/nested-tensor consumer pass strict checks and 38 owned
audits. Restrict this equation to evaluated modules, then use the chosen
canonical-content and weight coordinates. See [OldContentBraid](OldContentBraid.md).
See [OldAppendBraid](OldAppendBraid.md).
`ELVOldDistinctSlides` now supplies both distinct-colour coefficient
slides for the literal OLD dots and positive crossing. Its producer and
mixed/two-odd representable consumer pass strict checks and six owned
audits. `ELVModuleInductionSlides` now transfers a rectangular source
slide to whole induced module maps, with strict concrete OLD checks and
five owned audits. Apply the chosen pair flattenings before weight
transport. See [OldDistinctSlides](OldDistinctSlides.md).
`ELVInductionGridDistinctSlides` now supplies both rectangular pair
slides through the selected flattenings, with arbitrary changing
categories. Its producer and actual mixed/shifted OLD-content consumer
pass strict checks and three owned audits. Restrict to evaluated modules
and compare the independently chosen global dots in these same
coordinates. See [InductionGridDistinctSlides](InductionGridDistinctSlides.md).

The coefficient action remains literal ordinary precomposition on every
arrow, including inhomogeneous arrows. It must not be identified silently
with a supernatural representing map involving projection and twist.

The concrete factor action uses fixed-content module categories. The
fully faithful inclusion unit (#909), append-extension comparison (#910),
supported inclusion counit (#918), complementary restriction-extension
comparison and its tensor formula (#918/#920), and append tensor formula
(#924), together with the actual inner-unit tensor identity (#946), passed
original exact-head full CI and are integrated with full CI through #949. Complete compatibility of this canonical E/F
pair with the actual unit/counit, dots and crossings before transporting
the full factor presentation. No equivalence with arbitrary modules on
the whole old category is assumed.

Keep arbitrary old endpoints, empty Hom corners, height zero, full exterior
coefficients and source/target twists explicit. Other colours' exterior
coefficients are not a commutative ground ring.

The selected old-content extension and restriction comparisons now intertwine
signed dots on whole coends in both moving parities. Both producer/consumer
pairs and all 23 owned declarations pass scoped checks; full CI verified in #973.
See [ContentAppendDot](ContentAppendDot.md) and
[ContentAppendRestrictionDot](ContentAppendRestrictionDot.md). The generic
`ELVInductionSquareComposition` nested flattening formula and
`ELVWeightedPairAppend` composed append comparison are also scoped-checked
(70 owned declarations), with full CI verified in #973. Compare selected iterated
induction and crossings using these exact maps; fixed-content edges require
the changing-category grid, not an endofunctor identification. Chosen
content unit/counit and literal matrix attachment remain open.

## Independent braid and factor assembly

Use existing whole associativity and independent single-letter dots and pair
crossings. Canonical carriers and foundational relations are verified in
#832, distinct slides in #836. The prefix/suffix natural crossing families and corrected component braid
are full-CI verified in #901/#906/#894. The whole uncorrected natural braid
is retained from #939. Independent dot families and the whole corrected ordered
polynomial relation are implemented in #933/#934; both original exact heads
passed full CI. Use `ELVContentMixedBraidTransforms.contentMixedBraidTransform`,
preserving the original coefficient order and parameter twist.
The global homogeneous weight crossing `elvWeightCross` and whole canonical
pair coherence `elvWeightPairComparison_eq` are scoped-checked with paired
consumers; full CI verified in #972. The crossing retains the prescribed
equal-colour normalization and the zero coordinates without a double
predecessor. Pair/triple whiskering relation transfer and the full factor
action remain open. Retain intermediate-content transports, ordered polynomial
coefficients and full kernel parity.

A full-ELV factor family still requires the categorical inverse, these
multicolour relations and their naturality. Its distinct-colour factor mate
inverse (Brundan--Ellis (1.12)) remains open on arbitrary modules and the
chosen content/weight functors. `ELVDistinctIdealSpan` proves the distinct
outer-colour ideal identity (KKO I (9.3));
[full CI](https://github.com/apellis/odd-lean/actions/runs/41528015864) passed
at source head `62b981b8a0c47c013e34a7c813375f166b809c67`, integrated in #958.
The explicit signed crossing-coset PBW decoder, the balanced quotient by
both outer ideals, and the literal `SKM.rectangularMate` attachment are
scoped-checked on every old representable corner; full CI verified in #972.
`cyclotomicEquiv_symm_mk` gives the quotient inverse as `q ∘ decode`.
`moduleMate_crossing` identifies the evaluated mate with the crossing
column after canonical J, and `moduleMateEquiv_apply` attaches its inverse.
J twists the entire first tensor factor and retains the ordinary right
action. The mixed/exterior, all-odd, empty-word and zero-cutoff consumers
pass strict checks and audit all 208 owned declarations. Next extend this
inverse to every old module using the literal ordinary-right coefficient
kernels, then compare the chosen exact-content and weight functors.
See [DistinctCrossingDecoder](DistinctCrossingDecoder.md) and
[DistinctMateComparison](DistinctMateComparison.md). Existing ordinary-polynomial mate formulas and swapped raw
mixed-mate isomorphisms do not prove this full-ELV factor input. The older ordinary-polynomial
global constructor assumes local inversions and does not construct the
full exterior-coefficient family. The written pairing extension and balanced
cutoff schedule preserve the original weight realization; supplied CScalars,
its extension and the action restriction are verified in #864. This includes
parameterTwist compatibility and every RouquierMulticolour restriction field;
the construction still needs the concrete extended factor family. Choose
cofinal probe/reservoir weights by the written balanced schedule in the
pairing extension; the original weight group need not contain cofinal
dominant directions. Do not insert such an assumption on the original X.

`ELVRouquierMulticolour.elvRouquierMulticolour` now constructs all seven
multicolour fields for the selected full-ELV family, with the standing
highest-weight pairing and no supplied-family or inverse premise. The
fresh producer and mixed/asymmetric-odd consumer checks pass, including
all five owned audits, with full CI verified in #1014. The factor acts with `parameterTwist D Sc` and
retains original Sc in its presentation. Use in the compatible swapped pair remains. See [ELVRouquierMulticolour](ELVRouquierMulticolour.md).

## Weighted quotient and source detection

ELVCoefficientWindowTensor (#812) uses affine PBW freeness to retain the
entire bounded polynomial/exterior coefficient window. ELVJointPBWDetection
(#819) combines this injection with the actual truncated-kernel degree bound.
ELVBoundedSourceDetection (#820) embeds the exact ExtendedAtMost recovery
window with bounds fixed before cutoffs and jointly separates every source
Hom for finite colours. All three are full-CI verified.

Weighted module/map/isomorphism descent is verified in #825. The actual
quotient-induction counit is an even module isomorphism (#835); old induction
preserves the weighted annihilator, and its descended module is pointwise
isomorphic to truncated append induction (#840). Input-module naturality for every supernatural module map is verified in #868;
chosen comparison parity and generic induction/unit formulas are implemented in
#938/#940/#936, with original full CI. The canonical four-map comparison is
now evaluated on literal balanced coends by `ELVInductionSquareTensors`.
`ELVWeightedAppendTensors` and `ELVProbeAppendTensors` prove the selected
maps send every old tensor to its quotient tensor with unchanged vector,
including the exact units. Both signed-dot intertwining identities and
scalar hom/inverse parity passed strict mixed/vacuum consumers, owned
audits and [full CI](https://github.com/apellis/odd-lean/actions/runs/41535042662)
at source head `a3384f38`, integrated in #963. `ELVWeightedAppendAdjunction` now gives the
even identity-vector `weightedAppendRestrictionNaturalIso`, natural in every
supermodule map, and the exact ordinary counit comparison
`appendWeightedModuleIso_hom_counit`. The latter uses the prescribed counits
on literal restricted-module coends and the degree-zero induction component
of that same even restriction comparison. Its producer/consumer and all
26 owned declarations pass strict scoped checks; full CI for this addition passed in #972. Finish the chosen double-append crossing, inverse and normalized
content/weight compatibility; scalar ordinary adjunction remains separate.
See [InductionSquareTensors](InductionSquareTensors.md),
[WeightedAppendTensors](WeightedAppendTensors.md),
[WeightedAppendDot](WeightedAppendDot.md),
[WeightedAppendAdjunction](WeightedAppendAdjunction.md) and
[ProbeAppendTensors](ProbeAppendTensors.md).

`ELVInductionSquareTransform` defines the canonical raw-coend map
`coendSquareMap` for a commuting functor square; its tensor formula preserves the input
vector and maps the full coefficient arrow through that square.
`coendSquareMap_transform` proves compatibility with homogeneous
transformations when their literal coefficient families agree through the
square, retaining the full twist of arbitrary inhomogeneous arrows.
The producer, mixed old/truncated quotient consumer and all 15 owned
axiom checks pass strict scoped checks; full CI verified in #972. Identify the
raw map with the selected weighted append comparison using its literal
tensor formula, then prove two-letter flattening and chosen crossing
compatibility. See [InductionSquareTransform](InductionSquareTransform.md).

Keep the literal weighted coefficient ideal distinct from the paper's even
coefficient powers. `ELVCoefficientAnnihilation` is full-CI verified in #972.
The literal `CoefficientPowerModules` category now restricts selected old E/F,
ordinary unit/counit, dots, all module maps and supplied isomorphisms; parity
closure and the inherited Pi structure are also scoped-checked. These additions
retain full coefficients and need neither positive powers nor finite families
for their category restrictions. full CI verified in #973. See
[CoefficientPowerModules](CoefficientPowerModules.md) and
[CoefficientPowerParity](CoefficientPowerParity.md).

The coefficient bound and actual quotient-image calculation are scoped-checked:
`ELVCoefficientPowers` gives
R = sum_(surviving elementary a) (L_a-1) weight(a) + number of odd colours,
and `ELVCoefficientPowerSandwich` proves W_(R+1) contained in T contained in
W_N0 for the literal elementary-power ideal in the actual ELV coefficient
algebra, with the stated numerical lower-weight hypotheses. Quotient-algebra
arrows point weighted(R+1) -> power(T) -> weighted(N0); actual module functors
point weighted(N0)-modules -> T-modules -> weighted(R+1)-modules and retain
every vector space and homogeneous map component. All paired checks and the
48 owned-declaration audits pass; full CI verified in #973. See
[CoefficientPowers](CoefficientPowers.md),
[CoefficientPowerComparison](CoefficientPowerComparison.md) and
[CoefficientPowerSandwich](CoefficientPowerSandwich.md).

The actual A/T identification with SYM/(J+P), bounded coefficient detection,
parity and regular coefficient module are now scoped-checked. Extend this
module along the fully faithful empty coefficient embedding to construct the
chosen old power vacuum. Restrict finite-family/crossing inverse fields and
prove integer grading and contentwise nilpotence. Do not infer injectivity after imposing another
quotient. The arbitrary-T `TransformedIdeal` detection theorem still needs the
actual vacuum evaluation-kernel identification and final action attachment.

## Probe specialization and denominators

Dimension-free signed dot units at every mixed-word position, all heights
including vacuum, and actual content/weight dot isomorphisms are verified in
#807. Binomial specialization and original cyclotomic ideal descent are
verified in #813/#814; untruncated content-ring and append laws in #823.
The old content category and genuine probe module are verified in #831,
scalar module factorization in #842.

The exact scalar ideal images, ordinary quotient category, append, literal
word-corner equivalences and ordinary dot units are verified in #891.
The reverse matrix-entry cyclotomic-ideal lemma is verified in #863.
The chosen old-to-ordinary induction module comparison and quotient-inverse
unit-tensor formula are full-CI verified and integrated in #897.
`ELVProbeAppendTensors` supplies full-CI verified (#963) literal tensor/unit and signed-dot
formulas. `ELVProbeRestrictionComparison` now proves that old append restriction
preserves scalar coefficient evaluation and that its scalar descent equals the
chosen ordinary restriction. `probeRestrictionEqToHom_app` is identity in parity
zero and zero in parity one. The connected mixed/vacuum consumer and all 21
owned declarations are full-CI verified in #972. `ELVProbeCounitComparison`
now proves the selected ordinary counit composite equals the literal old counit
on every scalar-evaluated old target module and output word. Its paired consumer
and all 40 owned declarations pass strict scoped checks; full CI verified in #973.
Complete crossing, normalized cap and inverse-matrix transport. See
[ProbeCounitComparison](ProbeCounitComparison.md).
See [ProbeRestrictionComparison](ProbeRestrictionComparison.md).
The signed ordinary induction-dot unit is full-CI verified in
#893. The prescribed signed dot on the actual old append coend is also a
unit for scalar-evaluated modules, with the canonical probe specialization
full-CI verified and integrated in #927. Neither result requires finite
dimension or a coend-comparison premise. The selected ordinary model still needs
crossing, normalized-cap and inverse-matrix transport.

`ELVProbeEvaluatedCrossing` restricts the selected negative OLD crossing
through the full evaluated subcategory, preserving its literal component,
signed input naturality and square-zero equation. Its producer, concrete
occupied/empty/odd-input consumer and all 42 owned audits pass strict
checks and full CI in #1013. Continue with stored-target and weight transport, the braid and
the adjacent local record. See [ProbeEvaluatedCrossing](ProbeEvaluatedCrossing.md).

`ELVInductionGridRelations` proves both whole signed slides for the
chosen negative crossing. `ELVInductionGridLocal` and `ELVOldContentLocal`
assemble these with the prescribed actual matrix inverses into
`oldContentLoc`, with no local-record or inverse premise. All three
producers and both concrete consumers pass strict checks and 71 owned
audits, with full CI verified in #1014. Restrict the exact record to the evaluated full subcategory,
then handle canonical contents, absent predecessors and original weights.
See [InductionGridLocal](InductionGridLocal.md).

`ELVProbeEvaluatedLocal.probeEvaluatedLoc` now restricts that adjacent
record to the evaluated full subcategory with the original adjunction,
dots and crossing. All four inverse-entry component comparisons retain
the OLD maps definitionally for every row index. Producer and
both-parity/height/zero-overlap regular-probe consumer pass strict checks
and 182 owned audits. Transport this selected record through canonical
representatives, then handle absent predecessors and original weights.
See [ProbeEvaluatedLocal](ProbeEvaluatedLocal.md).
`ELVProbeEvaluatedBraid` also supplies the module and whole-transformation
equal braid for the selected evaluated negative crossings. Producer and
mixed-content/shifted/odd-input consumer pass strict checks and 35 owned
audits. See [ProbeEvaluatedBraid](ProbeEvaluatedBraid.md).

`probeOldActionDotIso` in `ELVProbeWeightDotUnit` constructs the inverse of
the chosen whole-weight dot over arbitrary weight fibres, including its
odd homogeneous inverse and absent predecessors. Its producer and
consumer pass strict checks and all 14 owned audits, with full CI verified
in #1014. The consumer retains
a nonzero actual induced unit vector at positive levels for both moving
parities. Use this unit in the concrete probe and denominator inputs.
See [ProbeWeightDotUnit](ProbeWeightDotUnit.md).

`ELVProbeRouquierData` now assembles the selected E, dots and total
equal/distinct crossing into the generator bundle with square and equal
braid. The specified adjunction retains F, unit and counit; the existing
finite-colour dot-unit result is attached. Producer and occupied
mixed/absent consumer pass strict checks and fourteen owned audits.
The unconditional RouquierFamily still requires canonical-weight local
records; remaining multicolour relations are separate. See
[ProbeRouquierData](ProbeRouquierData.md).

`ELVProbeWeightCrossing` now supplies the chosen negative crossing on
every original-weight fibre, including its stored-target formula, both
absent predecessor cases and whole square-zero relation. Its producer,
concrete mixed/odd-input consumer and all 55 owned audits pass strict
checks and full CI in #1013. Finish the signed slides, braid, local records and multicolour
fields. See [ProbeWeightCrossing](ProbeWeightCrossing.md).

`ELVProbeWeightPairInduction` supplies the literal supported two-step
weight coordinate and both absent-predecessor zero cases. Its producer,
concrete regular-probe consumer and all four owned audits pass strict
checks and full CI in #1013. `ELVProbeWeightDotWhiskering` identifies both independently
whiskered dots in the same supported coordinates as the chosen crossing;
its producer, concrete consumer and all four owned audits also pass,
with full CI verified in #1014.
`ELVProbeBlockDotComparison` identifies each selected stored-target dot
with the native induction-grid dot, with strict paired checks and four
owned audits, and full CI in #1014. Use these common coordinates to transport both signed
slides. See [ProbeBlockDotComparison](ProbeBlockDotComparison.md),
[ProbeWeightPairInduction](ProbeWeightPairInduction.md) and
[ProbeWeightDotWhiskering](ProbeWeightDotWhiskering.md).
The same module now exposes the supported pair coordinate and both dot
components for arbitrary colours, retaining the equal-colour statements
as specializations. Its generalized producer and extended mixed/shifted
consumer pass strict checks and seven owned audits. Use these actual
dot coordinates for the distinct-slide attachment.

`ELVProbeWeightTripleInduction` supplies the chosen three-step weight
coordinate with all stored intermediate targets and the actual zero module
in each missing-predecessor case. Its producer, mixed-content regular-probe
consumer and all eight owned audits pass strict checks. Compare both
independent crossing whiskerings through this same coordinate for the
global braid. See [ProbeWeightTripleInduction](ProbeWeightTripleInduction.md).

`ELVProbeBlockBraid` proves the braid for the two independently chosen
negative crossing whiskerings on the three stored-target block appends.
The literal OLD quotient relation supplies the grid input; no braid or
comparison premise remains. Its producer and occupied mixed/shifted
consumer pass strict checks and all 23 owned audits. Identify both global
whiskerings through the same triple coordinate next. See
[ProbeBlockBraid](ProbeBlockBraid.md).
`ELVProbeWeightBraid.probeOldActionEqualCross_braid` now proves the
whole-weight equal braid with the chosen associator, retaining both
independent crossing whiskerings in the same triple coordinate and
actual zero in every absent case. Producer and occupied/shifted consumer
pass strict checks and 22 owned audits. The equal braid is now available
for the probe family; local-record and multicolour assembly remain. See
[ProbeWeightBraid](ProbeWeightBraid.md).

`ELVProbeBlockNilHecke` proves both prescribed stored-target signed slides
and identifies both global dot totals in the selected double-predecessor
coordinate. Producer and occupied mixed/shifted consumer pass strict
checks and all 37 owned audits, retaining a nonzero induced unit vector.
`ELVProbeWeightNilHecke` now proves both global signed equations through
that same coordinate equality, including actual zero in both absent cases.
Its producer and occupied mixed/shifted consumer pass strict checks and
all four owned audits. Braid and local/multicolour assembly remain. See
[ProbeBlockNilHecke](ProbeBlockNilHecke.md) and
[ProbeWeightNilHecke](ProbeWeightNilHecke.md).

`ELVProbeWeightDistinctCrossing` supplies the positive crossing on the
selected weight E functors using all four stored-target appends. Its
producer and connected mixed/two-odd consumer pass strict checks and
all 72 owned audits, with full CI verified in #1014. The exact components, supported conjugation and
absent predecessors are retained. Transport the standard-cons mate
inverse through arbitrary canonical representatives and the same chosen
unit/counit maps. See [ProbeWeightDistinctCrossing](ProbeWeightDistinctCrossing.md).

`ELVProbeReindexInduction` constructs the canonical even append/reindex
comparison on OLD and evaluated module categories, with the original
composite unit/counit squares and both inverse identities. Its producer,
nontrivial-representative/odd-input consumer and all 45 owned audits pass
strict checks. Prove its tensor formula and dot/crossing comparisons,
then use these same maps for canonical local and distinct inverse transport.
See [ProbeReindexInduction](ProbeReindexInduction.md).
`ELVProbeReindexTensors` now proves the canonical comparison sends each
actual balanced tensor to the same arrow and vector at the reindexed
source. Its producer and arbitrary-vector/nontrivial-representative
consumer pass strict checks and 27 owned audits. Use this fixed comparison
for dot and crossing compatibility before canonical inverse transport.
See [ProbeReindexTensors](ProbeReindexTensors.md).
`ELVProbeReindexDot` now proves that this same canonical comparison
intertwines the chosen signed dot on every vector, whole module map and
evaluated component. Producer and mixed-parity regular-probe consumer
pass strict checks and 25 owned audits. The selected pair crossing and
local/distinct inverse records remain. See [ProbeReindexDot](ProbeReindexDot.md).

`ELVProbeEvaluatedDistinctCrossing` identifies the actual rectangular mate
of the chosen positive evaluated crossing under the specified lower and
upper j-adjunctions with the constructed invertible OLD mate. Its producer,
concrete mixed/two-odd consumer now also check the presentation
`crossMate` equality and invertibility. All 64 owned audits pass strict
checks. The 62-declaration rectangular-mate core passed full CI in #1013;
the two presentation corollaries passed full CI in #1014. Canonical-content and weight transport remain. See [ProbeEvaluatedDistinctCrossing](ProbeEvaluatedDistinctCrossing.md).

`ELVProbeEvaluatedDistinctMate` restricts the existing untruncated OLD
distinct mate and its inverse to the evaluated probe. The producer and
concrete mixed/two-odd consumer pass strict checks and all 54 owned
audits, with full CI verified in #1013. Its exact evaluated presentation cup-crossing-cap is identified
by `ELVProbeEvaluatedDistinctCrossing`; transport canonical stored
contents and original weights next.
See [ProbeEvaluatedDistinctMate](ProbeEvaluatedDistinctMate.md).

Scalar specialization is not faithful on the full coefficient algebra.
Positive-weight coefficient truncation cannot specialize to nonnilpotent
binomial constants. Finite-dimensionality requires the independently proved
raw finite append spanning (#766) and ordinary coefficient specialization.

Nilpotence is per target-content block, with an exponent uniform in input
modules but varying across a weight fibre (#778). Use verified componentwise
denominator inverses (#794), commutation and parity transport (#801),
actual adjunction transpose bounds (#790), and prescribed transposed norm
units (#811). The reservoir Sigma interface accepts literal transposed
source norms and target denominator units (#834); old whole-dot nilpotence
remains a sufficient corollary. Inverse-unit mate criteria are verified in
#817. The actual module-category universe instance is verified in #861. The literal even source norm is verified in #844; the odd source norms are
verified in #882. The prescribed coefficients, actual dotted-mate
isomorphisms, coefficient parity, both odd coefficient identities and raw odd
mate passed original exact-head full CI in #913/#917/#919/#922/#925/#930.
They are full-CI verified and integrated through #949. The raw even source norm
and `elvRawMixedEvenMateDot_isIso` now pass strict scoped producer/consumer checks.
`ELVRawCoefficientComparison` additionally proves one-sided uniqueness, the
inverse-first odd formula, exact earlier-coefficient identifications and the
parity-unified raw dotted mate. Degree-six even/odd and mixed identity-functor
consumers pass, including all eleven owned-declaration axiom checks; full CI verified in #972. See [ELVRawMixedEvenMate](ELVRawMixedEvenMate.md) and
[ELVRawCoefficientComparison](ELVRawCoefficientComparison.md). Finish compatible
factor-family identification and literal CrossCoeff input assembly. Do not assume a common exponent over
all contents or add another conditional factor-family wrapper.

`ReservoirVacuumDot` proves the actual occupied `dotImage` entry equals
postcomposition by the selected reservoir dot through the zero-probe
shift chart, for every Hom object. Producer and complete-factor two-odd
consumer pass strict checks and eight owned audits. The consumer retains
an independently nonzero odd regular-power coefficient. Evaluate this
whole-map square through the selected vacuum/word chart, then apply the
existing dot-coordinate formula. See [ReservoirVacuumDot](ReservoirVacuumDot.md).

`ELVReservoirWordValue.reservoirPath_value_heq` now identifies the
reservoir path value on the specified regular-power empty-word family
with the reversed selected E-word value, retaining the existing even
`pathChart`. Its producer and connected two-odd consumer pass strict
checks and twenty owned audits; the independent odd-coefficient product
and cyclic unit are nonzero in that same path value. Identify the eventual
swapped tensor-vacuum Hom input with this initial family before using
the comparison for observations. See [ELVReservoirWordValue](ELVReservoirWordValue.md).

`ELVPowerWordHomCoordinates` now passes fresh strict producer and
occupied-consumer checks, including all 48 owned audits. Its whole-Hom
linear equivalence, arbitrary coefficient, dot and crossing formulas
retain the selected word charts; the consumer has a nonzero two-odd Hom
and cyclic unit. Attach this model to the selected swapped Hom vacuum
input before asserting the final observation kernel. See
[PowerWordHomCoordinates](PowerWordHomCoordinates.md).

## Central augmented-matrix attachment

[CentralMatrixAttachment](CentralMatrixAttachment.md) specifies the
remaining fixed-output-content comparison from the actual `augPosMat`
and `augNegMat` to the two-sector model, including the negative signs,
absent pure paths and height zero. First identify the entire prescribed
reservoir cap rows and unit columns through the actual roundtrip-path
charts, at every dot power. The subsequent residual argument needs the
literal mixed bend expansions and positive coefficient-ideal membership
of the closed errors on every `Z : P.H t`. Existing contentwise nilpotent
ideals do not supply those memberships or the matrix square. Assemble
inverses componentwise, retaining bounds that vary with output content;
do not assume a common exponent over an entire weight fibre. This note
is a proposed attachment, not a constructed `CentralInvertible` instance.

## Final synthesis and verification

`SwappedVacuum/InverseCapMoments` is scoped-checked with occupied level-one
and degree-two concrete consumers and an owned-declaration axiom audit.
Its signed recurrence derives the principal cap and all positive-index
right moments from the slide, probe polynomial and coefficient-extraction
window. The window is now attached to the actual old empty-word
representable by `ELVUnitCoefficientRows`; `ELVVacuumMoments` and
`ELVVacuumSignedMoments` prove its full-coefficient raw normalization,
higher cyclotomic recurrence, all-exponent actual signed-dot comparison
and coefficient superlinearity. All three producers and concrete consumers
pass strict scoped checks, including all 62 owned-declaration axiom checks;
full CI verified in #972. See [UnitCoefficientRows](UnitCoefficientRows.md),
[VacuumMoments](VacuumMoments.md) and
[VacuumSignedMoments](VacuumSignedMoments.md). The occupied
[VacuumTwoOddCoefficients](VacuumTwoOddCoefficients.md) consumer checks both
operator orders and a nonzero independent exterior product in the actual old
vacuum; the super-opposite order is explicit. Attach the prescribed mixed
inverse maps and probe relation on the final power-quotient/swapped action;
no actual bubble-series interface is instantiated yet.
See [InverseCapMoments](InverseCapMoments.md). Its source head
`532683e2db4770b22950a5356863935e9c1d8851` passed
[full CI](https://github.com/apellis/odd-lean/actions/runs/41522225499) and
is integrated in #955.

`SwappedVacuum/NegativeCapMoments` now proves the negative-height
annihilation and low-unit window tests from the same signed slide and
probe polynomial. Its concrete occupied level-two/probe-level-one consumer
identifies the polynomial candidate with the final row of a nontrivial
whole augmented inverse. Strict local checks, the owned audit and
[full CI](https://github.com/apellis/odd-lean/actions/runs/41523687379) passed
at source head `39301885c8edff5e07c020246ff86ad5ebd0da5a`, integrated in #956. Next attach these tests to the actual module matrices,
then derive the all-height normalized bubble series.
See [NegativeCapMoments](NegativeCapMoments.md).

Construct the actual vacuum and normalized adjunction bubbles, using
ELVVacuumWordPairing and the existing VacuumCornerEvaluation and
AdjunctionBubbleSeries interfaces. Prove the bounded recovery identity, then
instantiate the field-linear observation consumer and apply finite-colour
and upward-to-oriented reductions.

Choose observation bounds, factor cutoffs and one coefficient truncation
before support bounds and terminating-series lengths. Do not assume
coefficient flatness, evenness of arbitrary kernels, uniform weight-fibre
nilpotence, or a finite-quotient automorphism from bounded-window substitution.

Update STATUS in place when obligations close. PROGRESS and README remain
pointers. Topic notes retain mathematical arguments; historical status text
is subordinate to STATUS. Distinguish proposed, scoped-checked and full-CI
verified results. Follow AGENTS.md for strict builds, concrete consumers and
the axiom policy.

## Unfinished attempts and restart points

All retired topic heads are retained in the primary research history; see
[ResearchHistory](ResearchHistory.md). Reachability preserves source, not verification.
The following are unfinished specializations, not completed inverse/action results:

| Target | Preserved source commit | Remaining obligation |
| --- | --- | --- |
| Weighted append tensor/dot/adjunction comparison | `97e4256b` | Historical proposed source, superseded by the full-CI verified tensor/unit and signed-dot formulas (#963) and full-CI verified `ELVWeightedAppendAdjunction` restriction/counit formulas (#972). Double-append crossing, inverse and normalized content/weight transport remain open |
| Scalar probe append tensor/dot comparison | `f145165c357d43b8241de20241cc6e911051f13e` | Historical proposed source; `ELVProbeAppendTensors` now has full-CI verified literal tensor/unit, parity and signed-dot comparison (#963). Chosen adjunction/inverse-matrix transport remains open |

Recover a file with `git show <commit>:<repository-path>`. These preserved source trees are outside the checked library until their
producer and paired consumer checks pass. Reachability is not a verification
claim. Earlier attempts hit normalization/conversion limits; redesign endpoint encodings and reusable comparison
lemmas rather than raising heartbeat or recursion budgets. The shared helper extensions
at the append restart commits have scoped checks only; the integrated #936 source has
its own full-CI boundary and must not be confused with those later extensions.
