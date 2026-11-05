# Odd nondegeneracy: mathematical handoff

## Research objective and order

**Phase 1 is proved.** `QuiverHecke.nondegeneracy_of_symmetrizer` proves
the conjecture for every symmetrizable Cartan superdatum, every commutative
ring with 2 invertible, every homogeneous scalar system and every supplied
`CScalars`, with no further hypotheses; the swapped route, exact heads and
integration evidence are in [STATUS](STATUS.md). Do not pursue
nonsymmetrizable Cartan data. The branch is complete when the odd analog and
its checked all-even specialization recover the most general cited even
nondegeneracy theorems over rings with 2 invertible; see
[FieldScopeBoundary](FieldScopeBoundary.md) for the parameter benchmark and
completion checks.

Next mathematical targets, in order:

1. **All-even comparison.** At parity identically zero, identify the
   presentation, normalizations, decorated matching families and bubble
   coefficients with the ordinary Kac–Moody 2-category of the even
   benchmark, and recover its basis theorem (including the grading) from
   `nondegeneracy_of_symmetrizer`. #1059 compares conclusions only.
2. **Phase 2.** Inhomogeneous parameters for symmetrizable data, covering
   the graded-coefficient generality of Brundan–Wang–Webster,
   arXiv:2505.22929v2, Theorem 5.6. First decide how the present `Scalars`
   presentation extends to positive-degree coefficients, then check which
   steps of the swapped route use `Sc.Homogeneous`.
3. **Normalizations.** Supply compatible `CScalars` under the benchmark's
   realization hypotheses, or prove a change-of-normalization comparison.

Start with [STATUS](STATUS.md) for established scope and claim boundaries.
[SwappedNondegeneracy](SwappedNondegeneracy.md) is the written proof.
This file records next mathematical dependencies, not session telemetry.
The sections below record the dependency analysis that led to the Phase 1
proof, including the superseded conditional vacuum route
(`QuiverHecke.nondegeneracy_of_vacuum_route`, #1056); they are retained as
restart context and are not open obligations of Phase 1.


## Work backward from the final theorem

**Recommended next approach: identify the smallest remaining inputs of the
final recovery theorem before expanding the supporting library.** The
suggestions below concern proof organization and possible simplifications;
they are not new checked results or changes to the Phase 1 hypotheses.

The factor, inverse and complete supported-action constructions have closed
substantial obligations. However, earlier descriptions of the remaining work
as observation, bubble attachment or final assembly concealed many separate
comparisons between content categories, weight categories, functors, matrices,
evaluated maps and quotient coordinates. A checked formula in one of these
representations does not automatically identify the maps used by the final
consumer. Repeatedly introducing intermediate comparison lemmas can enlarge
the library without closing that consumer's missing fields.

Start at `SKM.nondegeneracyConjecture_of_charZeroField` and retain its
already-proved reduction to the field input. For that input, use the existing
finite-colour and orientation reductions and
`nondegeneracy_of_restrictColours_vacuum_evaluations`. Work backward through
`UpwardModuleAction.toSwappedVacuumEvaluation` in
[SwappedVacuumRecovery](../../OddMath/QuiverHecke/SwappedVacuumRecovery.lean).
The complete supported action is already constructed; do not reopen its
presentation relations or require the stronger global relation record in
`SwappedVacuumObservation` merely to reach this endpoint.

Maintain a short dependency checklist in the current critical chain. For
each missing input, give its exact Lean statement, the chosen maps it must
refer to, the existing results that supply its inputs, and the named final
field that consumes it. Distinguish unproved mathematical equalities from
encoding/elaboration failures and from optional stronger identifications.
Do not count an intermediate theorem with an assumed compatibility equation
as having discharged that equation. Every additional helper should have a
specific consumer on this checklist.

The endpoint is now `VacuumRouteHypotheses` in
[VacuumRouteNondegeneracy](../../OddMath/QuiverHecke/VacuumRouteNondegeneracy.lean):
for the pairing extension of each finite-colour restriction at `(μ, 0)`, a
`VacuumRouteSector` on the constructed action. Its open inputs:

| Sector field | Boundary to preserve |
| --- | --- |
| `bubblesPositive : VacuumBubblesPositiveHeight` | Normalized left bubbles act as the substituted bubble series coefficients for `0 < ⟨hᵢ, μ⟩`, both parities. The inverse-column moment identities (#1051–#1053) hold for abstract inputs; instantiating the reservoir moments, column and probe on the tensor vacuum is the remaining step (#1055). |
| `bubblesNonpositive : VacuumBubblesNonpositiveHeight` | The same for `⟨hᵢ, μ⟩ ≤ 0`, via reciprocal series (#1057). |
| `coordinates : VacuumCoordinates` | An ideal contained in `ExtendedAtLeast D Sc t t' (vacuumCutoff t d - 2 * t.length.choose 2)` and a linear coordinate map from `A.V t'` to the quotient, from the canonical vacuum coefficient class (#1054). Audit whether a transported ideal suffices before requiring equality with a separately named ideal. |
| `chart : VacuumChartCoherence` | `evaluation`: each presented upward diagram applied to the substituted vacuum, read in the coordinates, is the class of the placed, substituted source coefficient; this joins the contextual dot/crossing layer charts to the literal affine action and coefficient placement (#1058). |

Raw coefficient actions or candidate polynomial caps alone do not supply the
bubble fields; the substitution, placement-sign and parameter-schedule
results do not discharge the coordinate or chart fields.

An informative next milestone is one complete bounded recovery instance
using the constructed supported action, its actual normalized bubbles and
its coordinate map, with every hypothesis discharged. Choose connected
mixed or two-odd data, retain nonzero independent odd coefficient directions,
and include a word pair that exercises crossings. This is a diagnostic of
the whole chain, not a replacement for the general theorem. The existing
`scripts/NonVacuity/SwappedVacuumBlock.lean` conversion example accepts a
vacuum block as an input; it does not itself construct such an instance.

Prefer a focused proof attempt with an explicit endpoint over broad parallel
helper development. Its outcome should be a closed final-field obligation,
a complete bounded instance, or a precise obstruction explaining why the
selected maps cannot yet satisfy the endpoint. If only further helpers
accumulate, reassess the representation and dependency choices before
expanding them again. Follow the existing encoding-redesign rule after
repeated elaboration failures; do not raise proof budgets.

Assess progress by closed endpoint obligations and newly discovered
dependencies. Counts of files, declarations, audits or agreeing assessments
do not supply a stable estimate of remaining effort. A passing build checks
the committed statements, including their hypotheses; it does not establish
that the missing inputs to a conditional recovery theorem can be constructed.

## Potential simplifications to assess before further transport work

### Prove recovery natively in the pairing extension

**Lean-checked, merged in #1050.** `PairingExtensionRecovery` proves
`homMap_upwardCoefficientMap`: the upward coefficient evaluation of `D` at
`μ`, followed by the exact presentation map, equals the evaluation of the
pairing extension `Dₑ` at `(μ, 0)` after `coefficientHomEquiv`. Hence
`nondegeneracy_of_pairingExtension_vacuum_evaluations`: vacuum evaluations
for `Dₑ` at the original weights `(μ, 0)` imply `NondegeneracyConjecture cs`
for `D`. The swapped action is already constructed on `Dₑ`, so the
`SwappedVacuumEvaluation` can be built where the action lives. This removes
the observation-quotient transport back to `D`, including the pulled-back
ideal below and the `PairingExtensionComposition`/`PowerIdeal` drafts. It
does not remove the extended-datum kernel bound, the vacuum observation or
the normalized bubble obligation, which are now stated for `Dₑ`.

### Pull back the observation ideal instead of identifying its generators

**Proposed, not Lean-checked.** The `SwappedVacuumEvaluation` interface takes
an arbitrary submodule `ideal`, its lower degree bound, and a coordinate map
with the required evaluation equation. It does not require that submodule
to be definitionally or propositionally equal to the named original-datum
power-word kernel.

Let `C` and `Cₑ` be the coefficient-extended affine Hom spaces before and
after the pairing extension, and let
`Φ := PairingExtension.coefficientHomEquiv D Sc s t : C ≃ₗ[k] Cₑ`.
This equivalence, its `sourceCoefficientHom` square, basis compatibility and
forward upper/lower filtration preservation are already checked in
[PairingExtensionPBW](../../OddMath/QuiverHecke/PairingExtensionPBW.lean).
Given the extended-datum observation submodule `Kₑ`, set

```
J := Submodule.comap Φ.toLinearMap Kₑ
Φbar : C ⧸ J ≃ₗ[k] Cₑ ⧸ Kₑ
coordinate := Φbar.symm.toLinearMap ∘ₗ coordinateₑ
```

The proposed argument still needs the following proofs:

- Derive inverse filtration preservation from the checked basis-preserving
  equivalence and degree equality. Forward preservation alone is insufficient.
  Then `Kₑ ≤ ExtendedAtLeast ... bound` implies the corresponding bound for
  `J`.
- Construct the induced quotient equivalence `Φbar` and its quotient-map
  formula; transport the literal evaluation equation through it using
  `coefficientHomEquiv_source` and the checked affine/action pullback square.
- Transport the coefficient action and substitution through
  `SKM.PairingExtension.coefficientEquiv`, and either conjugate the placement
  equivalence by `Φ` or prove agreement with the existing placement sign.
  Retain the required filtration bounds and the checked bubble pullback square.

If these supply the final evaluation interface, equality of `J` with the
named original coefficient-power/transformed-boundary ideal is unnecessary
for that route. In particular, do not automatically resume
`PairingExtensionComposition` and `PairingExtensionPowerIdeal` just because
their drafts exist. Determine which of their claims a final consumer still
needs. This may avoid the generator-by-generator ideal transport and some
coefficient-Hom composition work; it does not remove the extended-datum
kernel bound, actual vacuum observation or normalized bubble obligations.

### Keep comparisons as weak and local as their consumer permits

The recovery interface is indexed by a fixed external weight, word pair
and degree bound. Preserve the existing order in which those are chosen
before the truncation parameters. Do not require a simultaneous fixed-cutoff
evaluation on all words or a global first-boundary quotient identification
unless a named consumer needs it. Similarly, bounded recovery does not require
the bubble substitution to descend to an automorphism of the finite truncated
coefficient algebra; use its checked untruncated equivalence and bounded
filtration properties.

The current `bubbles_eq` field is an operator equality on the whole chosen
module. Checking a few vectors or only the vacuum is not a substitute for it.
Any proposed reduction to a coefficient-generated cyclic subspace would first
need a sufficient recovery criterion and the required invariance proofs;
no such shortcut is asserted here. The highest-risk remaining equations are
still the chosen inverse-row/bubble normalization and the actual canonical
observation formulas.

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
| Chosen residual coefficients and separated bend assembly | [6a4a989b42](https://github.com/apellis/odd-lean/commit/6a4a989b4269fd2802bf1a9422230ed2b68f368c) (complete source tree; sole parent is full-CI integration #1032) | Final chosen closure-degree transport, closure-ideal attachment, reservoir boundary degree, absent unit-window comparison, named padded inverse entries and separated bend/chart arguments remain incompletely checked. The tree also retains separately scoped-checked coefficient, support, finite-series and presentation additions awaiting their own full integration. Restore topical sources only. |
| Chosen closure degree and complete probe presentation | [a43c488268](https://github.com/apellis/odd-lean/commit/a43c4882682c9adc9d8d6030879ebd8ebc444108) (complete source tree) | Preserves the proposed all-output chosen coefficient degree, weighted-content kernel evaluation and denominator attachment, together with separately scoped-checked corrected braid and inverse-coordinate helpers. The complete closure dependency chain and factor integration remain unchecked in this snapshot. Restore topical files only. |
| Supported presentation, braids and represented degree | [8bb3b36820](https://github.com/apellis/odd-lean/commit/8bb3b3682097d0d065d1c95d60979f02c74a680d) (complete source tree) | Proposed general/corrected chosen braid fields, full probe package and coefficient fields, formal-sector support, literal two-context layer cells and represented integer grading retain incomplete checks. Separately scoped-checked local family, exact-content closure/vacuum and complete central matrix comparisons retain their own integration boundary. Restore topical files only. |
| Whole-weight, central matrix and observation synthesis | [a15c1058b0](https://github.com/apellis/odd-lean/commit/a15c1058b0bdb96069baa88e54ca9170e0510323) (complete source tree) | Proposed global local/principal/absent coordinates, triple braid paths/dots, augmented inverse evaluation, central path indices and actual coefficient-component bounds remain incompletely checked. Separately scoped-checked selected inverses, matrix bends and tensor-layer classes retain their full integration boundary. Restore topical files only. |
| Chosen local, mixed matrix and literal layer attachments | [1cc3b498df](https://github.com/apellis/odd-lean/commit/1cc3b498df47550c84691cfbe58896cc6d0aecc0) (complete source tree) | Canonical mate/upper-loop, evaluated missing-boundary, stored corrected-braid, supported mixed-coordinate, literal layer-matrix and probe-to-reservoir bend drafts retain incomplete checks. Separately scoped-checked stored inverse, nested braid, product/zero-boundary, principal reservoir and literal source-layer results retain their own full integration boundary. Restore topical files only. |
| Canonical local and central matrix attachments | [6b3aef99df](https://github.com/apellis/odd-lean/commit/6b3aef99dfb2669bf55d73bf5ea6531fb39a4314) (complete source tree) | Reindexed mate/crossing/dotted-row, pair/triple polynomial, outer-context Hom-entry and pure principal sigma drafts are not fully integrated. Separately scoped-checked distinct relations, local inverse transports and reservoir cap/unit rows are included but retain their own integration boundary. Restore topical files only. |
| Probe relations and selected vacuum attachment | [418df8069e](https://github.com/apellis/odd-lean/commit/418df8069eb8cbc07b48201ad4fccde9907b3f59) (complete source tree) | Evaluated local-record, representative tensor-comparison, global braid, selected reservoir-value and vacuum-dot drafts remain unverified. Whole-Hom word coordinates await fresh checks. The source also includes separately scoped-checked local records, reservoir presentation, path functor, dot units, signed slides and content braids awaiting their own full integration. Restore topical files only. |
| Probe and vacuum assembly successors | [82ddc2011b](https://github.com/apellis/odd-lean/commit/82ddc2011bb42715e1c5fb03359271160fa38a45) (complete source tree) | Whole-weight dot inverse producer passes; its occupied induced-vector consumer remains pending. Evaluated/weight crossing and adjacent local-record drafts are unverified. The reservoir-word comparison producer passes, but its complete factor consumer and vacuum-dot attachment remain pending. Restore only topical files and recheck; the tree also contains separately scoped-checked adjunction/dot, old braid, evaluated distinct-mate and pair-induction sources awaiting integration. |
| Whole weight probe dot inverse | [b9d9298e04](https://github.com/apellis/odd-lean/commit/b9d9298e04ce7847dac48e8d8574b5c1123befa4) (`OddMath/QuiverHecke/CyclotomicAction/ELVProbeWeightDotUnit.lean`) | Unverified whole-weight unit draft; repair the omit/docstring syntax and remaining transport details, then check the entire producer and a concrete consumer. |
| Adjacent old local record | [2cf3ffed79](https://github.com/apellis/odd-lean/commit/2cf3ffed792429c5f532e5d94b58da8dbd66d4aa) (`OddMath/QuiverHecke/CyclotomicAction/ELVInductionGridRelations.lean`) | Native module slides pass; the final two whole-Pi lifts remain unverified. Generic and concrete adjacent local constructors await complete paired checks. |
| Native multicolour structure | [3a6240c6bd](https://github.com/apellis/odd-lean/commit/3a6240c6bdac98cfddc4f55a2614f73b96d2f894) (`OddMath/QuiverHecke/CyclotomicAction/ELVRouquierMulticolour.lean`) | All seven chosen original-parameter fields and a concrete consumer passed scoped checks; fresh publication repeat and full integration remain separate gates. |
| Chosen whole-Hom word coordinates | [6d07efe699](https://github.com/apellis/odd-lean/commit/6d07efe699314d60e0bcd12b685122434e62be3b) (`OddMath/QuiverHecke/CyclotomicAction/ELVPowerWordHomCoordinates.lean`) | Producer and occupied consumer passed scoped checks, including a nonzero two-odd coefficient Hom; fresh publication repeat and full integration remain separate gates. |
| Global probe adjunction and dot | [ef53181050](https://github.com/apellis/odd-lean/commit/ef53181050a914dcfb682c996412ae41326e85c0) (`OddMath/QuiverHecke/CyclotomicAction/ELVProbeWeightAdjunction.lean`) | Both global right-adjunction and signed-dot producer/consumer pairs passed scoped checks; whole weight dot-unit and complete probe-family assembly remain open. |
| Local pre-adjunction preparation | [e661ef0b68](https://github.com/apellis/odd-lean/commit/e661ef0b682ae0876cbc60cdd4a038c65bd4df4c) (`OddMath/QuiverHecke/CyclotomicAction/ELVProbeVacuumPreAdjunction.lean`) | Private zero-lower braid and height-transport helpers checked; actual adjacent-record specialization and paired consumer remain pending. |

## Exact-content action attachment

Retain the content categories required by `SwappedActionAssembly` F4 and
(A1). `ELVContentHomSupport` now realizes arbitrary `SFun(T_b,W_c)` by
input projection and output zero extension, retains its selected objects
and maps, and proves all four selected primitive E/F functor equalities,
post E/F support, absent pre-E/post-F zero components and parity-shift
support. Strict actual tensor/two-odd affine collision/nonzero exterior
coefficient consumers audit all 35 declarations. `ELVContentHomClosure`
now supplies the whole even comparison isomorphisms and the generator-
stable full replete supported category, including parity closure and both
whole absent native zero functors. `ELVContentHomVacuum` places the literal
selectedHom in it using constructed all-input support. Strict paired
collision consumers audit all 64 and 16 declarations. Attach formal-sector
indices and restrict the chosen action; all inverse-entry arrows between
supported endpoints are retained. Use the checked zero functors before
transferring full factor inverses to the
zero-padded central matrix. The tensor vacuum `selectedHom` is the
supported initial family for this construction.

Do not infer a zero native composite from formal path absence on an
arbitrary object of `ProbeReservoir.H`: content collisions at a fixed
weight invalidate that inference. Existing `ELVWeightMatrixHeight` and
`ELVPowerWordWeight` consumers retain such collisions, and the pairing
extension does not remove them. This attachment realizes the approved
exact-content construction; it does not require changing the final
theorem's weight-group hypotheses.

## Exact source classes for power-word vectors

`ReservoirContexts.wordAt_eq_context` now identifies the entire actual
outer reservoir word with the prescribed reversed-word context functor
at arbitrary intermediate content, retaining its proved original-weight
transport. Strict connected mixed/two-odd/nonzero-terminal-content/
arbitrary-map/nonzero-exterior-output consumers audit all eighteen
declarations. Combine this left-context equality with the selected
right-Hom equality below, retaining the pair associator and endpoint
transports around the literal dot/crossing cell; see
[ReservoirContexts](ReservoirContexts.md).

`TensorReservoirWords.pathHomAt_eq_wordHom` now identifies the whole
selected tensor Hom along any actual reservoir path ending at zero with
the prescribed reversed-word Hom, using its proved original-weight
endpoint. The even regular-probe chart retains all coefficient carriers.
Strict connected mixed/two-odd/arbitrary-map/nil-path/nonzero-exterior-value
consumers audit all 25 declarations. Identify outer reservoir words at
arbitrary intermediate content with the chosen word-context functors,
then splice these charts into the literal layer/source-class square;
see [TensorReservoirWords](TensorReservoirWords.md).

`ELVTensorLayerClasses` now identifies the actual chosen ELV dot/crossing
Hom-entry evaluation under both word contexts with its physical OLD map
and original coefficient-one affine-layer quotient class. Strict occupied
connected mixed/two-odd/equal/distinct consumers prove nonzero normalized
input vectors and quotient classes and audit all thirty declarations.
Splice the selected tensor-vacuum word chart into the literal swapped
matrix, then attach the supported family/action and source bubbles;
no whole-Hom faithfulness is claimed. See
[TensorLayerClasses](TensorLayerClasses.md).

`ReservoirDistinctContextCoordinates.layerMap_reservoir_cross_ne_word`
now identifies the literal distinct matrix with the original factor
crossing in both reversed word contexts, retaining the actual right path
reindexing and endpoint transports. Strict complete two-odd ELV-pair/
nonempty-context consumer checks audit all sixteen declarations. All three
upward generator comparisons are now available in word coordinates;
specialize the intended tensor-vacuum and physical OLD quotient square.
See [ReservoirDistinctContextCoordinates](ReservoirDistinctContextCoordinates.md).
`ReservoirContextCoordinates` now identifies both actual reservoir path
contexts with their prescribed reversed word contexts. Its generic square
allows arbitrary inhomogeneous factor maps, and the literal dot and equal
crossing matrices satisfy the resulting word-chart equations. Strict
complete two-odd ELV-pair/nonempty-context consumers audit all thirteen
declarations. Retain the distinct endpoint reindexing and attach the
intended tensor-vacuum quotient square; see
[ReservoirContextCoordinates](ReservoirContextCoordinates.md).
`ReservoirVacuumCrossing.postCrossNe_reservoirVacuum` now compares the
prescribed distinct reservoir block with the factor crossing through the
exact source/target pair charts and target-sector transport, on every Hom
input. Strict complete two-odd ELV-pair checks audit all 17 declarations
and retain a nonzero odd exterior input. The literal matrix attachment
below retains both contexts; see
[ReservoirVacuumCrossing](ReservoirVacuumCrossing.md).
`ReservoirLayerDistinctCrossings.layerMap_reservoir_cross_ne` now proves
the literal distinct crossing matrix square under both outer contexts,
retaining the source endpoint cast and exact target-sector transport.
Strict complete two-odd ELV-pair/nonempty-context consumer checks audit
all twenty declarations. Join the word/context charts to the physical
OLD quotient square; see
[ReservoirLayerDistinctCrossings](ReservoirLayerDistinctCrossings.md).
`ReservoirLayerCrossings.layerMap_reservoir_cross_same` now supplies
the corresponding literal matrix-to-factor comparison for an equal-colour
crossing under both arbitrary path contexts and an arbitrary input matrix.
Strict complete two-odd ELV-pair/nonempty-context consumers audit all seven
owned declarations. The distinct comparison above retains its target-sector
transport; attach the intended OLD factor and quotient charts. The matrix fixture
makes no nonzero-entry or mixed-inverse claim; see
[ReservoirLayerCrossings](ReservoirLayerCrossings.md).
`ReservoirLayerGenerators.layerMap_reservoir_dot` now compares the actual
chosen upward-generator matrix with the prescribed reservoir factor dot,
retaining both arbitrary path contexts, append charts and the input
entry. Strict complete two-odd ELV-pair/contextual consumers audit all
four declarations; that matrix fixture does not claim a nonzero entry or
mixed inverse. Attach the intended OLD factor, word-functor charts and
existing quotient-class square; see
[ReservoirLayerGenerators](ReservoirLayerGenerators.md).

`HalfTurn.PowerWordLayerClasses.affine_class_square` now proves the
coefficient-one quotient-class square for every literal affine layer and
arbitrary actual word vector, with only the input-class premise. The map
is the physical contextual OLD dot/crossing, identified with the original
layer by proved half-turn and endpoint transports. Strict occupied mixed/
two-odd/nonempty-context consumers audit all 25 owned declarations.
Attach the selected supported family and actual swapped layer matrix,
then source-positioned bubble/coefficient action; see
[PowerWordLayerClasses](PowerWordLayerClasses.md).

`HalfTurn.ContextualOldGenerators.dot` and `.cross` now identify the
actual extended physical OLD generators with the half-turn of the
original affine layer, retaining arbitrary contexts, exact endpoint
transports and the negative equal crossing. Strict occupied mixed/two-odd
consumer checks audit all 25 declarations. Use these equalities with the
quotient coordinate square, then attach the actual path/layer matrix and
source-bubble maps; see [ContextualOldGenerators](ContextualOldGenerators.md).

`HalfTurn.PowerWordQuotientCoordinates.quotientEquiv` now identifies the
full source Hom modulo the exact transformed boundary and elementary-power
ideal with every actual regular-power word vector. Its inverse coordinate
and the chronological square for the existing signed OLD source map are
proved, including full inhomogeneous coefficient arrows and the literal
source-order sign. Strict occupied mixed/two-odd consumers audit all
eighteen declarations. The contextual generator equalities are checked above; next attach the actual layer matrix,
and identify source-placed bubbles with coefficient insertion. The complete
chosen factor and central matrix obligations remain prerequisites for an
observation; see [PowerWordQuotientCoordinates](PowerWordQuotientCoordinates.md).

## Dependency order and readiness

The distinct-relation and reservoir-row integration #1018 passed the full
warning-free build, global axiom audit and all concrete consumers at source
`e32a8614` (run 41701950651), integrated at `3014d062`. This verifies the
selected quadratic block, both global distinct slides, raw and nested
uncorrected multicolour inputs, reindexed inverse entries and pair chart,
all dotted reservoir rows, contextual vacuum words and Hom-entry evaluation.
The subsequent #1020 integration passed the full warning-free build,
global axiom audit and all concrete consumers at source `a2e6b551`
(run 41706422096), integrated at `97ad3177`. It verifies both exact probe
quadratic fields, the chosen reindexed crossing/mate and all dotted rows,
the missing-colour boundary including zero height, direct corrected braid
and triple-dot chart polynomial, both Hom contexts and exact every-vector
power-word quotient coordinates. Integration #1021 then passed the full
warning-free build, global axiom audit and all concrete consumers at
source `a4c9e781` (run 41710537064), integrated at `66fd1115`. It verifies
product inverse gluing, zero-boundary and even-chart transport, chosen
local generator/row components, the stored distinct-mate inverse,
whole-weight absent mixed coordinates, corrected nested/grid braids,
reservoir principal entries and the contextual source-layer class square.
Integration #1023 passed the full warning-free build, global axiom audit
and all concrete consumers at source `18ca3caa` (run 41714507812),
integrated at `17b99448`. It verifies stored missing-colour local inverses,
the zero lower cell and evaluated coefficient transport, exact bundled
slides, the evaluated stored corrected braid, occupied mixed/triple
coordinates and literal dot/equal/distinct reservoir matrix comparisons.
Integration #1024 passed the full warning-free build, global axiom audit
and all concrete consumers at source `362b01cf` (run 41718292713),
integrated at `5bfa9b77`. It verifies stored present-colour local inverses,
whole selected mate and dotted-row squares, exact global distinct probe
inversion, global crossing/cap/unit coordinates, pure probe principal and
probe-to-reservoir entries, evaluated finite coefficient expansions and
literal reservoir-context/source-class comparisons. Integration #1026
passed the full warning-free build, global axiom audit and all concrete
consumers at source `455117ec` (run 41721544509), integrated at
`afd225cc`. Its fourteen producers verify occupied principal and absent
local coordinates, evaluated finite inverses, specified weight paths and
three dots, both stored general braid forms, the ordered correction,
central path padding, the reverse mixed bend, probe dotted rows and
component coefficient bounds. Later whole local, central matrix and
supported-action additions retain their separate scoped-check/full-
integration boundaries below. Integration #1027 passed the full build,
global axiom audit and every concrete consumer at source `7f444a8c`
(run 41726688408), integrated at `2eb0ce1e`. Its nineteen producers
verify the chosen local probe family, exact-content full replete closure
and initial tensor vacuum, complete positive/negative native matrix
squares, selected triple crossing and reservoir-word coordinates, mixed
denominator units, shifted component bounds and matrix inverse naturality.
The remaining exact braid fields, represented positive closure degree,
central inverse and final observations are not established by this batch.

| Target | Ready to start? | Established inputs | Completion criterion / blocker |
| --- | --- | --- | --- |
| Fixed-content/weight matrix inverse assembly | Constructed in strict paired checks | Prescribed principal/unit/cap squares, supported and absent inverses, whole input-natural product assembly | Full integration gate pending; use the chosen maps in the factor |
| Reservoir factor family | Constructed in fresh strict paired checks | `elvRouquierFamily`, both local inverse families and all seven `elvRouquierMulticolour` fields with original Sc | Full CI verified in #1014; use the selected factor in the swapped assembly |
| Global probe family | In progress | Evaluated old subcategory, E/F/parity/product closure, entire natural dot inverse, old quotient square/slides and matrix inverses | Whole-weight adjunction/dot, dot inverse, equal crossing/slides/braid and generator data are full-CI verified through #1017; distinct slides and selected quadratic/multicolour inputs passed full CI in #1018; chosen local records and RouquierFamily passed full CI in #1027; finish the two exact multicolour braid fields and the complete package |
| Concrete swapped action | Factor interfaces available; instantiation incomplete | Ordinary and transposed blockwise denominator units, generic braid/inverse assembly | Supply complete probe/reservoir factors and chosen mixed inverses/coefficients; prove the literal central augmented-matrix squares and residual closure memberships |
| Vacuum and bubble recovery | Operator comparisons available; action attachment incomplete | Tensor-vacuum whole-module chart, prescribed cap polynomial identities, word/coefficient charts and joint source detection | Identify full chosen-action bubble/corner operators on every vector and construct observations |
| Vacuum path collapse | Full build, global axiom audit and all non-vacuity checks verified in #1010 | `SPath.subsingleton_of_upward_probe_zero`, `sum_of_upward_probe_zero` and the constructed `reservoirPath` for every upward labelled word | The even whole-functor identification with reservoir postcomposition passed full CI in #1014 in `ReservoirWordFunctor`; attach the selected vacuum value and contextual dot/crossing operators before constructing an observation |
| Final Phase 1 nondegeneracy | Blocked on concrete observations | Finite-colour reduction, upward/oriented equivalence, observation consumer and proved ground-ring descent | Supply observations for every required bound/word/weight for symmetrizable homogeneous data; inhomogeneous parameters belong to Phase 2 and nonsymmetrizable data are excluded |

## Reservoir principal matrix attachment

`Sigma.ReservoirPrincipal.sigmaEntry_reservoir_mate` and
`sigmaEntry_reservoir_coordinates` now identify the actual pure reservoir
principal entry with the selected shifted-adjunction mate and literal
factor `W.loc.sig`, through the prescribed cap/cup charts. Arbitrary full
Hom inputs and probe content are retained; the source path requires its
actual positive reservoir content. Strict two-odd full-factor consumer
checks include an independently nonzero exterior input and audit all 27
owned declarations. The probe principal and mixed bends, negative principal
minus, absent paths, complete augmented-matrix square and residual ideal
memberships remain separate. See [ReservoirPrincipal](ReservoirPrincipal.md).

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

Phase 2 target: `SKM.GradedCoefficientNondegeneracy D sy`
([GradedParameters](../../OddMath/SKM/GradedParameters.lean)). It already
implies the lower-degree ungraded statement
(`SKM.nondegeneracyConjecture_of_lowerDegree`). Next targets, in order
([Phase2Plan](Phase2Plan.md)): the reduction to the universal ring, to
characteristic-zero fields and to the truncated Rees parameters over
`K[h]/(h^N)` is checked; what remains is
`TruncatedRees.TruncatedReesNondegeneracy D sy`. Grade the KLR category over
`K[h]/(h^N)` as a `K`-linear supercategory with `h` in degree one (design in
Phase2Plan, step 2: coefficient-graded presentations and restriction of
scalars, `GradedSupercategory` unchanged);
rerun the nilpotence, kernel-degree and inverse-degree arguments of the field
route over such bases. The associated graded gives only spanning and is not
a route to independence. The missing pure monomials `u^r`, `v^s` of BWW are a
recorded open statement decision; `Scalars` is not enlarged.

The selected vacuum values, evaluated local/braid records, representative
tensor/dot/loop comparisons, rectangular slides and probe generator data
passed the full build, global axiom audit and all consumers in
[#1017](https://github.com/apellis/odd-lean/pull/1017) at `080bf70f`
([run 41698364466](https://github.com/apellis/odd-lean/actions/runs/41698364466)),
integrated at `88b36a6c`. Subsequent whole-weight distinct relations,
reindexed inverse attachments and matrix entries retain the scoped-check
boundaries stated below.

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
in #1014; the shared-grid refactor passed full CI in #1016. Restriction to evaluated fixed contents and weight transport
remain; these results do not yet prove the probe weight braid.
See [OldNestedBraid](OldNestedBraid.md).
`ELVProbeReindexLocal` transports both evaluated inverse records through
the even loop comparisons, preserving all finite identities and every
indexed entry. Strict producer and mixed-representative/both-height
consumer checks audit all 75 owned declarations. Forward mate and dotted
row compatibility with the chosen target generators is still required;
see [ProbeReindexLocal](ProbeReindexLocal.md).
`SKM.RouquierBoundaryTransport.ofIso` now transports a boundary
coefficient record through an even upper-loop chart, retaining every row
as the inverse chart followed by the original row. The cup square is an
explicit intermediate input; the single-edge append comparison must
supply it in the probe application. Strict actual missing-boundary
consumers, including nonzero top rows and count zero, audit all five
owned declarations. See [RouquierBoundaryTransport](RouquierBoundaryTransport.md).
`SKM.RouquierZeroLocal.ofCoefficients` now constructs the local record
from upper boundary coefficients and the actual lower-loop and double-cell
zero identities, retaining every inverse row and both orientations at
height zero. Strict mixed/nonempty/zero-height consumer checks include a
nonzero inverse top-row output and audit all 35 owned declarations. Apply
it to the selected evaluated/global loops using their computed zero
comparisons; see [RouquierZeroLocal](RouquierZeroLocal.md).
`SKM.RouquierProductInverse` now assembles both finite inverse orientations
on arbitrary products at a common height, with literal coordinate inverse
entries for every row index. Strict nonzero odd three-slot/two-block and
zero-window consumer checks audit all 42 owned declarations. Identify the
coordinate products with the chosen global mate and dotted rows before
using this for the weight local record; see
[RouquierProductInverse](RouquierProductInverse.md).
`ELVContentMissingLocal.contentMissingLoc` now constructs the untruncated
local record at arbitrary content missing the moving colour, including
both inverse orientations at height zero. Its coefficients are the
prescribed missing-colour inverse rows. Three changed producers and the
mixed/nonempty/shifted/zero-height consumer pass strict checks, auditing
74 owned declarations; the legacy vacuum consumer also passes. Restrict
to evaluated modules, transport the upper append to its stored content,
and compare the absent global lower loop with zero; see
[ContentMissingLocal](ContentMissingLocal.md).
`ELVProbeMissingStoredLocal.probeMissingStoredLoc` now constructs the
selected missing-colour local inverse with the stored upper adjunction
and dot and the constructed zero lower cell. Both zero-height orientations
are retained. Strict mixed/nonempty/reordered/odd-input/zero-height
consumer checks audit all 22 owned declarations and prove a nonzero
output of the actual inverse top row. Attach the absent global coordinates
and combine with the present-colour local records; see
[ProbeMissingStoredLocal](ProbeMissingStoredLocal.md).
`ELVProbeZeroBoundary` now constructs the zero object, endocell and
even zero adjunction in every evaluated content category, with zero
identity after any actual postcomposition. Strict mixed/nonempty/odd-map/
zero-level consumers audit all thirty declarations and prove that the
ambient vacuum and actual append identities remain nonzero. The stored
local constructor above combines these with the boundary coefficients;
identify the absent global coordinates; see [ProbeZeroBoundary](ProbeZeroBoundary.md).
`ELVProbeMissingStoredCoefficients.probeMissingStoredCoefficients` now
constructs the finite boundary record for the literal stored-target
adjunction and dot, with the chart and every unit-column comparison
proved. No compatibility or inverse premise remains; count zero is
included. Strict mixed/nonempty/reordered/odd-input consumers prove a
nonzero stored top-cap output and audit the construction. The stored
local record above combines the zero lower cell; attach global coordinates; see
[ProbeMissingStoredCoefficients](ProbeMissingStoredCoefficients.md).
`ELVProbeMissingCoefficients.probeEvaluatedMissingCoefficients` now
constructs the prescribed finite boundary record for the actual evaluated
append adjunction and dot. All native row components and the top cap
are retained, including count zero. Strict mixed/nonempty/odd-input/
zero-count consumer checks prove a nonzero evaluated top-cap output and
audit all 68 owned declarations. Transport these coefficients through
the checked stored upper-loop chart, then attach the zero lower local
record; see [ProbeMissingCoefficients](ProbeMissingCoefficients.md).
`ELVProbeAppendUpperLoop` now supplies the selected even evaluated
upper-loop chart and the whole unit-column square for every exponent,
without a lower predecessor. Strict mixed/nonempty-missing/reordered/
shifted consumer checks audit all 36 owned declarations. Transport the
constructed evaluated missing-colour coefficients through this chart,
then attach the actual zero lower cell and global coordinates; see
[ProbeAppendUpperLoop](ProbeAppendUpperLoop.md).
`ELVProbeReindexUnitColumns` now preserves the unit and every dotted
column through a single arbitrary append comparison, without assuming
a lower predecessor. Strict mixed/nonempty-missing/reordered/shifted
consumer checks audit all 22 owned declarations. Lift the upper-loop
chart to evaluated categories and transport the constructed missing
boundary coefficients; see [ProbeReindexUnitColumns](ProbeReindexUnitColumns.md).
`probeOldRouquierFamily` now constructs the complete chosen local
probe family on original weights, including both local inverses, with
no factor or inverse premise. Its generators, restriction and right
adjunction retain their literal definitions, and its dot remains a
unit. Strict twisted mixed/normalized-left-adjunction consumer checks
audit all nine declarations. Attach the two remaining multicolour braid
fields to finish the complete factor presentation; see
[ProbeRouquierFamily](ProbeRouquierFamily.md).

`ELVProbeWeightLocalInverse` now assembles the occupied and absent
coordinates into both entire natural inverse records for the prescribed
global principal and dotted rows. Strict mixed/positive/negative/both-
zero-height consumer checks audit all 34 declarations. No finite-block
or independent-root hypothesis is used. Attach these two records to
the already chosen local generators to construct the probe family; see
[ProbeWeightLocalInverse](ProbeWeightLocalInverse.md).

`ELVProbeWeightSupportedInverse` now supplies both prescribed finite
inverse orientations at every occupied output coordinate, using the
checked stored inverses and exact principal/cap/unit charts. Strict
regular mixed/positive/negative/both-zero-height consumers audit all
53 declarations. Combine with the missing-predecessor inverses below
to assemble the whole product and complete local record; see
[ProbeWeightSupportedInverse](ProbeWeightSupportedInverse.md).

`ELVProbeWeightAbsentInverse` now transports the missing stored local
record to both exact global inverse orientations, retaining the actual
zero lower coordinate and every unit/power column. Strict regular mixed/
missing/zero-height consumers audit all 65 declarations. The explicit
cutoff compatibility identifies content and categorical heights. Finish
the supported coordinate inverse and glue both cases over the whole
weight product; see [ProbeWeightAbsentInverse](ProbeWeightAbsentInverse.md).

`SuperSumInvTo.at` and `SuperSumInvFrom.at` now evaluate the complete
finite inverse records at any object, retaining the principal parity
component and every forward and inverse dotted total. Strict nonzero
three-slot odd/empty-window consumers check both orientations and audit
all 36 declarations. Apply these to the selected stored local inverses
before whole-weight product gluing; see
[AugmentedInverseEvaluation](AugmentedInverseEvaluation.md).

`probeOldActionCross_via_total` now retains the actual selected crossing
through arbitrary supported lower blocks and a common upper block, with
the prescribed stored component and equal-colour minus. Strict nonempty
mixed/two-odd/equal/distinct/nonzero-append consumer checks audit both
declarations. Attach its two independently whiskered triple squares,
then the corrected and general braid fields; see
[ProbeWeightCrossPathCoordinates](ProbeWeightCrossPathCoordinates.md).

`ELVInductionBraidCube` and the ordinary/evaluated stored-target braid
now retain all twelve append edges and the equal-colour minus on every
crossing. `probeStoredBraid` has exactly the uncorrected colour condition
and no supplied braid or comparison premise. Strict connected mixed/
two-odd/repeated/all-equal/interior-parameter/nonzero-input consumer
checks audit all 4, 92 and 89 declarations. Attach the six global
crossing coordinates and assemble the exact uncorrected field; see
[ProbeStoredBraid](ProbeStoredBraid.md).

`probeOldWeightTriplePolynomial_component` now retains the entire
ordered original-Sc correction through the same chosen triple chart,
with the parameter-twisted acting family and all three prescribed dots.
Strict mixed/three-odd/nonzero interior-parameter/nonzero-append
consumer checks audit all 28 declarations. Combine this polynomial
square with the six crossing squares and the stored corrected braid;
see [ProbeWeightTriplePolynomial](ProbeWeightTriplePolynomial.md).

`ELVProbeWeightTripleDots` now identifies all three independently
whiskered chosen dots with their prescribed stored append components
in one supported triple chart. Strict occupied mixed/three-odd consumers
retain nonzero append outputs and audit all fifty declarations. Use
these coordinates for the ordered correction polynomial, then attach
both global braid fields; see [ProbeWeightTripleDots](ProbeWeightTripleDots.md).

`ELVProbeWeightPathCoordinates` now retains the entire chosen pair and
triple induction coordinates through specified supported intermediate
blocks and the actual signed dot total. Strict occupied mixed/nonempty
consumer checks retain nonzero append outputs and audit all eight
declarations. Attach the crossing through common path vertices, then
three-strand polynomials and exact global braid fields; see
[ProbeWeightPathCoordinates](ProbeWeightPathCoordinates.md).

`ELVProbeWeightLocalMateCoordinates.probeOldWeightRouquierMate_comparison`
now identifies every parity component of the occupied global principal
with its selected stored mate. The actual negative crossing and both
chosen adjunctions are retained, with no inverse premise. Strict mixed
regular/parity-shifted consumer checks audit all 55 declarations. Use
this square together with the all-exponent rows to transport supported
local inverses, then glue all weight coordinates; see
[ProbeWeightLocalMateCoordinates](ProbeWeightLocalMateCoordinates.md).

`ELVProbeWeightCapCoordinates.probeOldWeightCapPower_total_comparison`
now retains the actual global dot-power/counit row through its exact
predecessor equality at every exponent. Strict mixed regular/parity-
shifted/nonempty/all-exponent consumer checks audit all 25 declarations.
Together with the unit comparisons below, these supply every row needed
for product inverse gluing. The principal coordinate is now checked above;
see [ProbeWeightCapCoordinates](ProbeWeightCapCoordinates.md).
`ELVProbeWeightUnitCoordinates.probeOldWeightUnitPower_total_comparison`
now retains the actual global unit followed by every dot power through
its selected successor coordinate, including missing lower predecessors.
Strict mixed regular/parity-shifted/empty-content/all-exponent consumer
checks audit all 27 declarations. Attach cap and principal coordinates,
then glue the local inverses over the whole product; see
[ProbeWeightUnitCoordinates](ProbeWeightUnitCoordinates.md).
`ELVProbeAppendToLocalInverse.probeAppendToInvPos` and
`probeAppendToInvNeg` now construct both prescribed finite inverses at
arbitrary stored representatives. The chosen mate and rows agree with the
transported original fields, and every inverse entry is retained literally.
Strict pure/reordered mixed/both-height/zero-height/off-diagonal/all-index
consumer checks audit all 64 declarations. Attach the whole-weight
coordinates and glue products; local memberships/slides remain separate.
See [ProbeAppendToLocalInverse](ProbeAppendToLocalInverse.md).
`ELVProbeAppendToMateReindex.probeAppendToMate_reindex` now proves the
whole selected evaluated mate square through the even lower and upper
loop comparisons, retaining original source and stored target generators.
Strict reordered mixed/odd-input/regular/parity-shifted consumers audit
all 31 declarations. Together with the dotted-row squares below, copy both
transported inverse orientations into the present-colour local record;
see [ProbeAppendToMateReindex](ProbeAppendToMateReindex.md).
`ELVProbeAppendToRowReindex` now proves both whole evaluated dotted-row
squares for every exponent, and identifies the canonical source rows
with the original evaluated adjunction/dot fields. Strict mixed/reordered/
nonempty/all-exponent/odd-input consumer checks audit all 38 declarations.
Combine with the selected mate square to construct the present-colour
local record and whole-weight assembly; see
[ProbeAppendToRowReindex](ProbeAppendToRowReindex.md).
`ELVProbeReindexLoopAction` retains whole natural-transformation
components under reindexing and the prescribed standard evaluated mate,
with its original adjunctions and negative equal crossing. Strict mixed
regular/parity-shifted consumers audit all sixteen declarations. Combine
these with the loop charts for the canonical mate square; see
[ProbeReindexLoopAction](ProbeReindexLoopAction.md).
`ELVProbeReindexLoopComponents` identifies both selected even loop
comparisons with the OLD maps used in the proved mate square. Strict
reordered mixed/shifted/odd-input consumer checks audit all fourteen
owned declarations. Use them in the whole evaluated mate and dotted-row
comparisons; see [ProbeReindexLoopComponents](ProbeReindexLoopComponents.md).
`ELVProbeAppendToRows` now identifies every selected dotted unit/counit
row with its prescribed OLD homogeneous components, for arbitrary stored
targets, dot exponents and parities. Strict mixed reordered/odd-input
consumer checks audit all 68 owned declarations. Combine these with the
representative-change row squares to identify the canonical inverse
fields; see [ProbeAppendToRows](ProbeAppendToRows.md).
`ELVProbeAppendToLocalFields` now supplies the selected negative crossing
and all-parity native component formulas for that crossing, every dot
power and the literal chosen mate at stored targets. Strict mixed
reordered/shifted consumer checks audit all 72 owned declarations. Use
these component formulas with the even loop comparisons, then attach
all dotted rows to the transported finite inverse; see
[ProbeAppendToLocalFields](ProbeAppendToLocalFields.md).
`ELVProbeReindexRows` now preserves both prescribed dotted unit/counit
rows through the same append comparisons, for every exponent including
zero and arbitrary module input. Strict mixed reordered-content/shifted
consumer checks audit all 36 owned declarations. Combine these with the
whole mate square to identify the evaluated/natural local fields and
transported inverse. The absent-lower-predecessor sectors and whole-weight
assembly are still separate; see [ProbeReindexRows](ProbeReindexRows.md).
`ELVProbeReindexMateNatural` now proves the whole OLD module-map mate
square through the exact lower append comparison and restricted upper
comparison. Strict mixed reordered-content/shifted consumer checks audit
all 39 owned declarations. Attach the dotted unit/counit rows and the
canonical evaluated fields; see [ProbeReindexMateNatural](ProbeReindexMateNatural.md).
`ELVProbeReindexMate` now proves the all-vector chosen negative-mate
square through the same two append comparisons, preserving every
coefficient arrow and twist. Strict producer and mixed reordered-content/
shifted consumer checks audit all 38 owned declarations. Lift to whole
module/natural maps and attach the prescribed dotted unit/counit rows
before constructing the canonical local record. See
[ProbeReindexMate](ProbeReindexMate.md).
`ELVProbeWeightMixedMateInverse.probeOldRouquierData_invNe` now proves
the exact bundled distinct sideways-crossing inversion on the whole
weight product, from the chosen supported mate and both absent zero
coordinates. It retains the natural inverse and its degree. Strict
asymmetric two-odd/twisted/occupied/absent/odd-input consumers audit all 81
declarations and both inverse identities. No mixed-inverse premise
remains; complete the local family and remaining braid fields. See
[ProbeWeightMixedMateInverse](ProbeWeightMixedMateInverse.md).
`ELVProbeWeightMixedMateComparison` now retains the actual upper unit
and lower counit through the occupied mixed-coordinate equalities.
Strict asymmetric mixed-parity regular/parity-shifted weight consumers audit
all 61 declarations. Paste these with the selected crossing square and
apply the stored mixed inverse; see
[ProbeWeightMixedMateComparison](ProbeWeightMixedMateComparison.md).
`ELVProbeWeightMixedCoordinates` identifies the occupied mixed-loop
endpoints, arbitrary-target induction maps and the exact selected block
crossing through the original product-coordinate equalities, at every
parity. Strict asymmetric mixed-parity consumers audit all 63 declarations.
Paste the actual cup and cap to attach the stored inverse to the global
mixed mate; see [ProbeWeightMixedCoordinates](ProbeWeightMixedCoordinates.md).
`ELVProbeWeightMixedMate` now defines the actual chosen global sideways
mate, its parity and coordinate formula. Adding a distinct colour cannot
create a missing predecessor, so both absent coordinates are zero and
the prescribed map is invertible there. Strict occupied/empty-content
consumer checks audit all 33 owned declarations. Compare supported
coordinates with the stored-target inverse, then assemble global `invNe`;
see [ProbeWeightMixedMate](ProbeWeightMixedMate.md).
`ELVProbeReindexDistinctMate` now constructs the prescribed distinct-mate
inverse on every stored-target OLD input and full evaluated category.
`probeAppendToCrossMate_eq` and `_isIso` retain the chosen positive
crossing and both selected right adjunctions; only distinctness is
required. Strict mixed/two-odd/odd-input-natural consumer checks audit all
132 owned declarations. Attach the absent and supported weight coordinates
and global `invNe` field; see [ProbeReindexDistinctMate](ProbeReindexDistinctMate.md).
`ELVProbeReindexCrossing` now identifies the prescribed positive crossing
through the selected pair comparison on all raw vectors, whole module
maps and full evaluated categories. Strict mixed regular-probe/odd-map
consumer checks audit all 179 owned declarations. The stored distinct-mate inverse is checked above; attach the weight coordinates and negative equal normalization; see
[ProbeReindexCrossing](ProbeReindexCrossing.md).
`ELVProbeReindexPair` now gives the exact upper-then-lower append
comparison on raw and evaluated modules, with evenness and an all-vector
nested tensor formula retaining both coefficient arrows. Strict producer
and mixed reordered-content/odd-input consumer checks audit all 67 owned
declarations. The selected positive crossing square is checked above; attach the distinct mate next;
see [ProbeReindexPair](ProbeReindexPair.md).
The prescribed lower and upper local loops now have even representative
comparison isomorphisms in `ELVProbeReindexLoops`; strict producer and
mixed-content consumer checks audit all 38 owned declarations. Attach
the chosen mate and dotted unit/counit maps before transporting the
original inverse record. See [ProbeReindexLoops](ProbeReindexLoops.md).
The signed probe slides, content braid, representative adjunction comparison,
triple coordinates and whole-Hom word coordinates passed the full build,
global axiom audit and all consumers in [#1016](https://github.com/apellis/odd-lean/pull/1016)
at `cf38def4` ([run 41695267103](https://github.com/apellis/odd-lean/actions/runs/41695267103)).

`ELVInductionGridBraid` and `ELVOldContentBraid` now supply the same
comparison on four consecutive content categories and the prescribed
negative braid on every old content module. Both producers and the
mixed/shifted/nested-tensor consumer pass strict checks and 38 owned
audits. Restrict this equation to evaluated modules, then use the chosen
canonical-content and weight coordinates. See [OldContentBraid](OldContentBraid.md).
See [OldAppendBraid](OldAppendBraid.md).
`ELVInductionRectangularTriple` now compares both independently whiskered
rectangular crossings through one chosen triple flattening, even with
different intermediate content categories. Strict producer and concrete
mixed/three-odd/distinct-middle-category consumer checks audit all four
owned declarations. Assemble the six signed braid paths and ordered
correction next; see [InductionRectangularTriple](InductionRectangularTriple.md).
`ELVInductionRectangularWhiskering` extends both chosen composition
comparisons to whole maps with distinct source and target append functors.
Strict producer and changing-content mixed/three-odd consumer checks audit
all seven owned declarations. Use these squares for the six independent
rectangular triple braid paths; see
[InductionRectangularWhiskering](InductionRectangularWhiskering.md).
`ELVModuleMulticolourBraid` proves the three-map balanced transfer with
the matching superopposite signs in both path orders. Strict producer and
concrete OLD-path consumer checks audit all four owned declarations.
Attach the literal OLD braid and rectangular nested comparisons; see
[ModuleMulticolourBraid](ModuleMulticolourBraid.md).
`ELVInductionTripleCorrection` now constructs the source polynomial
supernaturality and proves the whole ordered original-Sc correction
operator equality, without a supplied naturality or braid premise.
Strict mixed/three-odd/interior-parameter consumer checks audit all eight
owned declarations. Identify the literal OLD coefficient correction and
selected nested/evaluated braid difference; see
[InductionTripleCorrection](InductionTripleCorrection.md).
`ELVInductionTriplePolynomial` now evaluates the ordered original-Sc
three-dot correction on every balanced tensor, retaining the reversed
twisted-source polynomial and entire kernel twist. Strict mixed/three-odd/
interior-parameter consumer checks audit all ten owned declarations.
Attach the whole operator and literal OLD braid difference; see
[InductionTriplePolynomial](InductionTriplePolynomial.md).
`ELVProbeSlideFields` now proves the two exact bundled distinct slide
fields for the selected probe data with twisted parameters. Strict
connected mixed/interior/two-odd/disconnected-parameter consumers audit
all eight declarations. Combine these fields with the separately proved
quadratics and the remaining braid/inverse attachments; see
[ProbeSlideFields](ProbeSlideFields.md).
`ELVProbeWeightCrossCoordinates` now retains the selected weight crossing
through its exact product coordinates as the stored-target crossing,
with negative equal and positive distinct normalization. Strict occupied
mixed/two-odd/equal/distinct consumers audit all 23 declarations and retain
nonzero append outputs. Attach the whole-weight braid paths through the
common triple coordinates; see
[ProbeWeightCrossCoordinates](ProbeWeightCrossCoordinates.md).
`ELVProbeWeightTripleCoordinates` now retains both intermediate canonical
blocks and an arbitrary common final stored target for the whole supported
triple induction coordinate. Strict occupied mixed-parity/nonempty and
three-absent-case consumers audit all eight declarations. Use these
coordinates for the chosen whole-weight braid fields; see
[ProbeWeightTripleCoordinates](ProbeWeightTripleCoordinates.md).
`ELVProbeEvaluatedStoredMixedBraid.probeStoredMixedBraid_polynomial`
now proves the whole corrected braid in the full evaluated categories
with arbitrary stored representatives and all seven chosen append edges.
Strict occupied non-cons/mixed/three-odd/interior consumers audit all 89
owned declarations and retain nonzero append outputs. Attach the selected
whole-weight triple coordinates and exact presentation fields; see
[ProbeEvaluatedStoredMixedBraid](ProbeEvaluatedStoredMixedBraid.md).
`ELVProbeStoredMixedBraid.probeOldStoredMixedBraid_polynomial` now
proves the whole corrected relation at arbitrary stored lists, with all
seven append edges and the original-Sc correction in the actual nested
dots. The source equation is discharged using the full-content forget
map and literal OLD quotient; no relation premise remains. Strict
non-cons stored/mixed/three-odd/interior consumers audit all 96 owned
declarations. Lift to evaluated categories and whole-weight fields next;
see [ProbeStoredMixedBraid](ProbeStoredMixedBraid.md).
`ELVInductionCorrectedGrid` now retains seven different append edges
and six categories in the whole chosen corrected braid, with three
specified flattenings and independent nested dots. The intermediate
coefficient equation is discharged by the OLD quotient in the strict
mixed/three-odd/interior consumer; all 25 owned declarations are audited.
Specialize the stored-content grid and discharge its source equation,
then attach the evaluated and whole-weight generators; see
[InductionCorrectedGrid](InductionCorrectedGrid.md).
`ELVModuleCorrectedBraid` now transports the corrected relation across
three different composite source functors to the whole module equation.
Its source-coefficient equation is an explicit intermediate input,
discharged by the actual OLD quotient relation in the strict mixed/
three-odd/interior consumer; all eleven owned declarations are audited.
Specialize the stored-target grid and discharge the same source equation
before asserting an action field; see [ModuleCorrectedBraid](ModuleCorrectedBraid.md).
`ELVOldCorrectedNestedBraid.oldNestedMixedBraidMap_polynomial` now proves
the chosen nested corrected braid in the actual three independent dot
whiskerings, with the explicit negative-equal/positive-distinct
normalization. Strict mixed/three-odd/interior/odd-kernel consumers audit
all thirty owned declarations. The ordinary OLD braid algebra is supplied;
transfer the relation to evaluated/stored-target and whole-weight
functors next. See [OldCorrectedNestedBraid](OldCorrectedNestedBraid.md).
`ELVInductionTriplePolynomialMaps.inductionTripleFlattening_polynomial`
now transports the entire ordered original-Sc correction into the three
independently whiskered nested dots through the same chart. Strict mixed/
three-odd/interior/changing-content consumer checks audit all five owned
declarations. Combine this with the signed direct braid and six crossing
squares, then transfer to evaluated and weight functors; see
[InductionTriplePolynomialMaps](InductionTriplePolynomialMaps.md).
`ELVInductionTripleDots` now supplies all three whole nested-dot squares
through the same chosen triple flattening, across four arbitrary
categories. Strict mixed/three-odd/changing-content/shifted consumer
checks audit all five owned declarations. Use these to transport the
entire ordered correction polynomial and combine the six crossing
squares; see [InductionTripleDots](InductionTripleDots.md).
`ELVOldCorrectedInductionBraid.oldDirectMixedBraid_polynomial` now proves
the signed direct braid difference with its negative equal crossing and
original-Sc ordered correction. Strict occupied mixed/three-odd/interior/
odd-kernel consumer checks audit all sixteen owned declarations. Use the three checked nested-dot squares to transport the correction,
then lift the corrected relation to evaluated and weight functors; see
[OldCorrectedInductionBraid](OldCorrectedInductionBraid.md).
`ELVOldTriplePolynomial.oldTriplePolynomial_operator` now identifies the
whole original-Sc correction operator with the polynomial in all three
independent OLD dots, retaining their exact source positions and every
interior coefficient. Strict occupied mixed/three-odd consumer checks
audit all twenty owned declarations. The signed direct braid
difference is checked above; transfer the dots through the chosen nested charts; see
[OldTriplePolynomial](OldTriplePolynomial.md).
`ELVOldNestedMulticolourBraid.normalizedNestedTripleCross_braid` now
proves the actual nested uncorrected braid with independent pair
whiskerings, negative equal and positive distinct crossings, through the
six selected triple squares. Strict occupied mixed/three-odd/shifted
consumer checks audit all nineteen owned declarations. Evaluated/canonical
weight attachment and the original-Sc repeated-outer correction remain.
See [OldNestedMulticolourBraid](OldNestedMulticolourBraid.md).
`ELVOldMulticolourInduction.directTripleCross_braid` now proves the whole
direct triple-module braid using the literal OLD source relation, with no
braid premise. Strict occupied mixed/three-odd/shifted/interior-parameter
consumer checks audit all four owned declarations. Attach the selected
nested crossings and negative equal normalization; the repeated-outer
correction remains separate. See [OldMulticolourInduction](OldMulticolourInduction.md).
`ELVOldMulticolourBraid` proves both uncorrected and repeated-outer
coefficient braids for the independently appended positive OLD crossings,
including nonzero interior parameters. Strict producer and mixed/three-odd
consumer checks audit all eleven owned declarations. Transfer through the
changing-category balanced charts with their superopposite signs and
negative equal crossings before asserting the original-Sc action fields.
See [OldMulticolourBraid](OldMulticolourBraid.md).
`ELVOldDistinctQuadratic` now proves the literal source square and
original-Sc signed polynomial comparison, followed by the actual balanced
double-induction tensor equation. Strict producer and mixed/interior/two-odd
consumer checks audit all six owned declarations. The chosen changing-content
flattenings and global probe quadratic remain. See
[OldDistinctQuadratic](OldDistinctQuadratic.md).
`ELVOldDistinctSlides` now supplies both distinct-colour coefficient
slides for the literal OLD dots and positive crossing. Its producer and
mixed/two-odd representable consumer pass strict checks and six owned
audits. `ELVModuleInductionSlides` now transfers a rectangular source
slide to whole induced module maps, with strict concrete OLD checks and
five owned audits. Apply the chosen pair flattenings before weight
transport. See [OldDistinctSlides](OldDistinctSlides.md).
`ELVOldPairPolynomial` identifies the literal source polynomial with
the independent OLD pair dots, and `ELVInductionPairPolynomial` proves
its supported-power, interior-monomial and whole linear operator
evaluation. Both producers and mixed/interior/two-odd consumer pass strict
checks and all 23 owned audits. Transport through the chosen flattening
to the selected block and global dot operators; see
[OldPairPolynomial](OldPairPolynomial.md).
`ELVProbeQuadraticFields` now supplies both exact bundled presentation
fields, `probeOldRouquierData_quadZero` and `probeOldRouquierData_quadNe`,
using its literal crossing and independently whiskered dot powers with
original Sc. Strict connected/interior/two-odd and disconnected parameter-2
consumer checks audit all ten owned declarations. Assemble the remaining
multicolour fields; see [ProbeQuadraticFields](ProbeQuadraticFields.md).
`ELVProbeWeightQuadratic.probeOldActionDistinctCross_quadratic` now
proves the whole original-weight crossing square as the ordered
original-Sc polynomial of both actual global dots over `parameterTwist D Sc`.
Closed block-natural and absent-source-zero cases are included. Strict
mixed/interior/two-odd/shifted/absent consumer checks audit all seventeen
owned declarations. The exact quadratic fields are checked above; complete the remaining
multicolour fields; see [ProbeWeightQuadratic](ProbeWeightQuadratic.md).
`ELVProbeBlockQuadraticDots` now identifies the actual selected crossing
square with the original-Sc ordered polynomial of both independently
chosen dot totals on whole underlying module maps. Its generic chart
transport is `ELVInductionPairPolynomialMaps`; both producers and the
mixed/interior/two-odd consumer pass strict checks and all 36 owned audits.
Lift to closed block-natural maps and all weight sectors next; see
[ProbeBlockQuadraticDots](ProbeBlockQuadraticDots.md).
`ELVProbeBlockDistinctQuadratic` now identifies the actual two selected
positive crossings over `parameterTwist D Sc` with the balanced transform
of the literal original-Sc signed polynomial. Its generic changing-content
transport is `ELVInductionGridQuadratic`; both producers and the concrete
mixed/interior/two-odd consumer pass strict checks and all 43 owned audits.
Identify this polynomial with the two independently chosen dot operators,
then assemble the global field including absent sectors. See
[ProbeBlockDistinctQuadratic](ProbeBlockDistinctQuadratic.md).
`ELVProbeWeightDistinctSlides` now proves both signed distinct slides
for the actual global crossing and independently whiskered dots on all
original weights, using both selected coordinates and the actual zero
source at absent predecessors. Strict mixed/two-odd/shifted/absent
consumer checks audit all ten owned declarations. Attach these fields
to the complete probe presentation after the other fields are constructed.
See [ProbeWeightDistinctSlides](ProbeWeightDistinctSlides.md).
`ELVProbeBlockDistinctSlides` proves both distinct-colour slides of the
prescribed stored-target crossing and independently whiskered dots, with
strict mixed/two-odd/shifted consumer checks and all 40 owned audits.
The same two product coordinates and absent predecessors are now
handled by `ELVProbeWeightDistinctSlides`.
See [ProbeBlockDistinctSlides](ProbeBlockDistinctSlides.md).
`ELVInductionGridDistinctSlides` now supplies both rectangular pair
slides through the selected flattenings, with arbitrary changing
categories. Its producer and actual mixed/shifted OLD-content consumer
pass strict checks and three owned audits. Restrict to evaluated modules
and compare the independently chosen global dots in these same
coordinates. See [InductionGridDistinctSlides](InductionGridDistinctSlides.md).

`SwappedAssembly.ReservoirDottedFactorCoordinates` now composes the full
path transports and identifies every actual reservoir cap row/unit column
with the prescribed `homContentPostCap/Cup` and literal factor adjunction
and dot words. Strict producer and occupied two-odd consumer checks audit
all 32 owned declarations. The pure principal crossing block, mixed blocks
and full matrix square remain; see
[ReservoirDottedFactorCoordinates](ReservoirDottedFactorCoordinates.md).

`SwappedAssembly.ReservoirDottedAdjunctionRows` now computes the actual
reservoir branches of every dotted cap row and cup column, including
exponent zero, for arbitrary Hom inputs. Strict producer and occupied
two-odd full-factor consumer checks audit all 19 owned declarations.
The retained inner transports are now composed in
`ReservoirDottedFactorCoordinates`; principal/mixed blocks and
residual-error closure remain open. See
[ReservoirDottedAdjunctionRows](ReservoirDottedAdjunctionRows.md).

`SwappedAssembly.ReservoirLayerEntries` now collapses the actual
upward/probe-zero layer sums to the given single `layerEntry`, preserving
both whiskers and every append transport. Strict producer and supplied
complete-ELV-pair matrix consumer checks audit both declarations. This is
a theorem about a supplied complete factor pair; the matrix fixture has
no nonzero-vector claim. Attach the intended OLD record, chosen path
coordinates and signed quotient/vacuum values next; see
[ReservoirLayerEntries](ReservoirLayerEntries.md).

`ELVTensorHomContexts` now retains both inner and further outer E-word
contexts on the literal dot/crossing Hom entries, with the chosen context
charts and all-vector formulas for arbitrary input Hom maps. Strict
occupied nonempty mixed/two-odd consumers audit all 25 owned declarations.
Transport through the actual path/layer matrices and attach the signed
quotient classes to `ev_layer`; see [ELVTensorHomContexts](ELVTensorHomContexts.md).

`ELVTensorHomEntries` now proves the surviving reservoir dot/crossing
entry squares for arbitrary source Hom objects, whole input maps and
every vector, using the same selected word charts. Strict occupied mixed
and two-odd consumers audit all sixteen owned declarations. Its note gives
the specified supported `Gs`/`Ys` recipe; outer-E contexts are now checked above. Unique-path
matrix transports and quotient-class attachment to `ev_layer` remain.
Evaluation at the regular probe is not asserted faithful on all Hom
transformations. See [ELVTensorHomEntries](ELVTensorHomEntries.md).

`ELVTensorVacuumWords` now extends the literal chosen tensor Hom to every
reservoir word context, with even value and full coefficient charts,
all-vector dot/crossing formulas and whole Hom coordinates preserving
every old-word generator. Strict occupied mixed/two-odd consumers in
nonempty contexts audit all 46 owned declarations. Attach these exact
comparisons to the layer matrices and literal `ev_layer`; the completed
action record remains separate. See [ELVTensorVacuumWords](ELVTensorVacuumWords.md).

`ELVTensorVacuumGenerators` now identifies the one-E dot and two-E
equal/distinct crossing out of the selected tensor Hom vacuum with the
prescribed reservoir word operators. The same `selectedIso` and literal
regular probe are used, with all-vector formulas on every formal block.
Strict producer and occupied two-odd consumer checks audit all 33 owned
declarations. The arbitrary contexts are now checked above; attach to the completed
record; see [ELVTensorVacuumGenerators](ELVTensorVacuumGenerators.md).

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
and cyclic unit are nonzero in that same path value. The specified tensor
Hom input is now identified with this family by `ELVWeightTensorVacuum`;
attach the resulting chosen word comparisons to the literal observations. See [ELVReservoirWordValue](ELVReservoirWordValue.md).

`ELVWeightTensorVacuum` now constructs the full-product tensor Hom from
the OLD probe category and its explicit regular evaluated probe, zero on
every nonempty formal block even when weights coincide. Its even
`selectedIso` identifies evaluation at that probe with the actual
`ReservoirWordValue.initialValue`, with the every-vector scalar/unitor
formula and unchanged tensor coefficient. Producer and occupied two-odd
consumer pass strict checks and 39 owned audits; the independent odd
product remains nonzero. `ELVTensorVacuumWords` now carries the chosen
reservoir dot/crossing maps through this comparison in every word context;
attach the literal swapped layers next. See
[ELVWeightTensorVacuum](ELVWeightTensorVacuum.md).

`ELVPowerWordHomCoordinates` now passes fresh strict producer and
occupied-consumer checks, including all 48 owned audits. Its whole-Hom
linear equivalence, arbitrary coefficient, dot and crossing formulas
retain the selected word charts; the consumer has a nonzero two-odd Hom
and cyclic unit. `ELVTensorVacuumWords.homEquiv` now attaches these
coordinates to the specified tensor Hom after evaluation at its regular
probe. The literal layer evaluation and final observation kernel remain. See
[PowerWordHomCoordinates](PowerWordHomCoordinates.md).

Both chosen probe braid equations are now attached. The general field is
full-CI verified in #1030; the corrected whole-weight relation and literal
dotted field pass strict paired checks with 107 and 53 owned audits.
`probeOldRouquierMulticolour` assembles all seven prescribed fields, and
`elvProbeReservoir` constructs the intended untruncated OLD probe/truncated
ELV reservoir factor with its normalized shifted left adjunctions and
invertible probe dot. Their strict mixed/two-odd/nonzero-append consumers
audit five and nine declarations. All four additions passed full CI in #1032. `ELVProbeDenominatorUnits` now constructs the chosen mixed
coefficient, its inverse and supernaturality; `ELVProbeCoefficientExpansion`
proves both component finite series with no supplied inverse or global
nilpotence premise. Their strict consumers audit 38 and 17 declarations.
`SupportedFactorPaths` and `SupportedGeneratorEntries` identify its actual
paths and restrict the literal generators, including the constructed mixed
crossing; strict nonzero affine two-odd consumers audit 10 and 21 declarations.
These four producers passed full CI in #1033. Supported matrix-presentation
transport and named native inverse data are now scoped-checked below; central
inversion and the final observations remain open.

## Central augmented-matrix attachment

The chosen factor, its full multicolour records, actual mixed coefficient,
inverse identities and supernaturality are constructed. Integrations #1032
and #1033 passed full build, global axiom audit and every concrete consumer.
#1033 verifies the component coefficient expansions, arbitrary stored-content
closure/boundary coordinates, native coefficient contraction equations,
output projection, supported paths/generators and all four supported pure
factor inverse interfaces. Its source head is `928b4da392aa4b66a08f02c89f08fa3e0b1f14e2`,
run 41753142717, merged at `55b95505ef22e26c520f836bb42018bab1ff648d`.

The following chosen closure/boundary and supported-vacuum results passed
full CI in #1035 at source `34fe3ca0bd1a2893bf0adab17c6da4fe71f6e035`,
run 41756477511, merged at `bb83ab02b9811a59c9fc3ab03a33689f0da94cf7`.

- `ELVReservoirClosureDegree` proves degree `2*d_i*(r+s+1)` for both
  reconstructed source coefficients of the literal chosen principal
  closures, on every output content. Its 150-declaration audit and concrete
  consumers retain both height orientations, both parities, arbitrary
  modules and all absent blocks. The coordinate chain uses inverse
  uniqueness, weighted-to-OLD kernel comparison, and represented source
  reconstruction; no integer grading on arbitrary module Homs is assumed.
  See [ChosenReservoirClosureDegree](ChosenReservoirClosureDegree.md).
- `ELVReservoirClosureIdeal` places the two coefficients in the content
  coefficient grading and their literal native postcomposition closures,
  after output projection, in level one of the jointly nilpotent ideal.
  Arbitrary surrounding morphisms are allowed. All eight public APIs are
  exercised on an occupied odd fixture; 15 declarations are audited.
- `ELVWeightWindowInverseCoordinates` and `ELVAbsentWindowInverseCoordinates`
  attach the chosen finite inverse slots. `ELVReservoirBoundaries` retains
  the literal `W.loc.boundaryPos/boundaryNeg` and reconstructs their source
  actions. `ELVReservoirBoundaryDegree` proves source degree `2*d_i*(r-j)`
  on every stored output for finite inverse slot j, with 144 audited
  declarations. The absent negative unit boundary can be nonzero: its
  diagonal acts as identity on a proved nonzero vacuum vector. Preserve
  this branch when using positivity for r>j. `ELVReservoirBoundaryIdeal`
  now places these off-window actions and their literal native contractions
  in level one, with arbitrary surrounding maps. Its strict paired consumer
  exercises all eight public APIs and audits all 19 declarations.
- `Sigma.ReservoirWindowInverseData` names the chosen padded reservoir
  principal/window entries, their inverse equations and occupied/absent
  coordinates. All 85 declarations are audited. Use these exact entries
  with the native contraction equations in `CentralInverse.FactorClosures`
  before applying the closure and off-window coefficient-ideal lemmas.
- `ELVProbeBendEvaluation`, `Sigma.FiniteBendEvaluation` and
  `ELVProbeFiniteBends` give both actual finite insertion series from the
  constructed coefficient, probe unit and component reservoir bound.
  `Sigma.BendDotCoordinates` identifies all four signed raw dot charts;
  `SKM.RouquierHomBendMonomials`, `Sigma.BendSeriesAlgebra` and
  `Sigma.BendWindowMonomials` give the separated native cap/cup monomials
  and inverse-power algebra. Their paired consumers include nonzero
  actual probe objects and noncommuting operator examples.
- `SupportedMatrixModules` and `SupportedPresentation` transport the
  literal matrix generators and every relation through the full supported
  inclusion. Their constructor retains `SwappedObligations`, including
  central inversion and closed moments. `SupportedTensorVacuum` supplies
  the even supported path comparison for the selected tensor Hom; its
  affine two-odd consumer proves a two-letter value is nonzero.
  `SupportedTensorContexts` gives its factor-map square in both literal
  selected-vacuum path contexts; strict nonzero coefficient-class consumers
  audit all 20 declarations. Literal composed layer entries remain next.

The cap-boundary and canonical word-observation integration #1043 passed
the full warning-free build, global axiom audit and every concrete consumer
at source `019a0ef4d12f4a8612f0e73e73b73f1a6196df3c` (run 41776984044),
merged at `fe83891043af7ac2edf2de75c1b916243d8d2fe7`. The canonical all-height
left mate, complete distinct permutation, native braid application, complete
supported upward action and full matrix coefficient observation passed
all the same gates in #1044 at `dfc547fd854300dc5f1a028aa0c299b011723f0b`
(run 41779494448), merged at `775c1c59c8856c84af87efcd6ebf429553fe7bc5`.
Subsequent vacuum-row, source-value, layer and moment attachments below
retain their strict paired-check boundary until their own full integration.

The whole-output separated formulas are now scoped-checked in
`ELVProbeContentBends` (50 owned declarations), with the fixed-exponent
transport of `ELVOutputDotBounds` (10), the generic separated equations
(93 and 41), and the component specialization (25). The common finite
length is chosen before quantifying over input modules. The actual
padded probe slide and every Aut cap/cup power are also scoped-checked
in `SupportedProbeSlideWindow` and its three helpers (57 declarations).
`SupportedTensorDotEntries` attaches the literal vacuum dot matrix in
both nonempty contexts (25 declarations). `Sigma.PaddedBendWindowEquations`
and `ELVProbePaddedContentBends` now attach both whole-output sums to the
literal padded matrix entries, including both absent corners (10 and 13
declarations). `ELVContentHomZero` constructs the needed canonical zero
object (7). `CentralInverse.SeparatedClosures` derives all three mixed
closed-error memberships by finite sums (9), with a nonzero square-zero
coefficient-ideal consumer. All these successor pairs await full integration.

The chosen central inverse is now full-CI verified in #1037. `ReservoirWindowCoefficientIdeal`
attaches J0/J1, both principal signs and every finite contraction to the named
padded inverse (32 owned declarations). `ResidualComparisonNegative` and
`SignedResidualWindows` cover all six signed-height cases (5 and 22).
`Sigma.PaddedResidualInversion.centralFactorMatrix_content_isIso` and
`centralAugmentedMatrix_isIso` assemble the actual matrix inverses on every
supported input, including both height-zero orientations. Their strict
nonzero two-odd collision consumer audits all nine declarations. No inverse,
series, closure or nilpotence premise remains beyond the standing data,
symmetrizer and homogeneous parameters. The all-sector extension below is full-CI verified in #1039.
See [CentralMatrixAttachment](CentralMatrixAttachment.md).

`SupportedTensorCrossEntries` now gives both literal crossing matrices
(70 declarations); `SupportedTensorDotClasses` and `SupportedTensorCrossClasses`
give the all-vector affine quotient-class squares (39 and 95), with nonzero
independent odd products and both contexts. These strict pairs do not yet
package the whole-sector observation.

Next discharge the following dependencies in order.

1. `SupportedAugmentedInverse` now constructs both augmented inverses and
   all ten same-colour identities at every supported input and outer sector,
   using `ELVProbeTransposeNorms` and `OffCentralAugmentedMatrix`. Its strict
   nonzero consumer audits 14 declarations. `SupportedSupernaturality` and
   `SupportedInterchange` supply restricted parity/naturality and interchange
   (28 and four audited declarations). `SupportedAction.pointwiseObligations`
   now supplies the constructed distinct-colour permutation and all remaining
   relation fields; `pointwiseUpwardModuleAction` gives the complete supported
   upward action with no extra relation premise. Its strict native tensor-family
   consumer passes, auditing 49 declarations across the action, inversion and
   supernaturality modules. No raw ambient inverse is asserted.
2. The distinct-colour package is now scoped-checked. The native cap proof
   covers `h_i(a) ≤ max(d_ij−1,0)`; in the complementary range the next
   i-weight has height strictly above `d_ij`, where the complete cup identity
   applies. Both canonical contractions preserve the actual maps.
   `RouquierCanonicalDistinctLeftMate.canonicalLeftMateInvertible` proves
   `LeftMateInvertible T T.leftAdjoints` from the multicolour record at every
   weight, with no extra premise. Its source and actual allweight two-odd
   consumer pass, with both owned declarations audited.
   `DistinctPureEntries` and `DistinctPureReservoirEntry` now have native
   consumers for both pure entries. `ELVProbeSigmaPermutation` assembles
   the full native permutation with no mate or pure-entry hypothesis;
   its strict both-order consumer passes. This package is now used directly
   in the checked supported interchange and presentation assembly. The older braid spine's
   actual universe-generalized application now passes its constructed
   supercategory consumer and audit of all 1,348 declarations across 98
   modules; no mathematical hypothesis is changed. A standalone allweight cap identity and
   closed-delta scalar simplification are not needed by this completed
   invertibility argument.

3. `SupportedTensorFamilies`, `SupportedTensorRows`, `SupportedMatrixLayers`
   and `SupportedTensorRowLayers` now construct the whole-sector nonzero
   tensor matrix and prove its occupied row and literal layer-action formulas
   (50, 25, five and 18 declarations audited; full CI #1039).
   `SupportedTensorCoefficientAction` now constructs its raw coefficient
   action on every path Hom; `SupportedTensorUnitObservation` defines its
   source-unit quotient observation. The global append/pair charts and
   regular-probe observation are full-CI verified in #1041 in
   `ELVTensorWordChartCoherence`, `ELVTensorPairChartCoherence` and
   `ELVTensorWordQuotientObservation`. `ELVTensorContextChartCoherence` and
   `SupportedTensorPathChartCoherence` now join every outer-context chart
   to the actual path chart. `ELVTensorWordCoefficientChart` gives its
   global coefficient square; `SupportedTensorMatrixCoefficients` acts
   on the entire matrix. `SupportedTensorObservationLinearity` and
   `SupportedTensorWordObservation` provide the exact word-indexed linear
   observation. `SupportedTensorRowCoefficientAction` and
   `SupportedTensorMatrixRowCoefficients.tensorOriginalWordEntry_coefficient`
   now prove exact whole-matrix coefficient equivariance through the
   original-weight entry. `SupportedTensorCoefficientChart` and
   `SupportedTensorCoefficientUnitObservation` give the all-vector signed
   quotient formula. The canonical source-unit chart and its inverse-map
   formula are checked, including the affected word-observation consumers.
   `SupportedTensorMatrixCoefficientObservation.tensorMatrixCoefficient_observation`
   now combines these into the unchanged canonical observation of the full
   matrix coefficient action; its nonzero mixed-coefficient consumer passes.
   `SupportedTensorVacuumObservation.tensorOriginalWordEntry_vacuum` now
   identifies the canonical vacuum row with its exact source isomorphism;
   its strict consumer audits 31 declarations. The additive typed
   `tensorOriginalSourceUnit_wordValue` normalization passes the extended
   Unit consumer with 70 audits. `SupportedTensorEntryLayers` transports
   the literal layer action to chronological whole-Hom postcomposition,
   with a complete-action/nonzero-matrix consumer and 30 owned audits.
   `SupportedActionLayers` identifies the complete presented layer with
   this native restriction/operation/extension map. `ReservoirWordFunctor`
   now exposes its exact nil/cons comparison components (definitions
   unchanged; 111 owned audits), needed for evaluation coherence.
   `SupportedTensorEntryLayerCharts` now proves whole-Hom conjugacy for
   the actual dot, equal crossing and distinct crossing, instantiated at
   canonical row charts; repeated/distinct nonzero two-odd consumers and
   all 118 owned audits pass. Finish the vacuum quotient value and the
   compatibility of these chart changes after
   regular-probe evaluation, and the contextual layer laws.
   A nonzero cyclic input does
   not establish injectivity of observation on all matrices.
4. `CentralInverse.VacuumWindow` and `Sigma.VacuumInverseWindow` extract
   the chosen finite vacuum rows (full CI #1037). The four modules described
   in `ProbeWeightLeftCap` now identify the normalized whole-weight probe
   counit with the native vacuum cap through an even source chart (full CI
   #1039). `ELVProbeWeightPreCap` now inserts it into the actual pre-Hom
   counit; the successor, upper-loop and full vacuum dot charts are
   full-CI verified in #1041.
   `ELVTensorVacuumMomentMaps` supplies raw moments on every input vector.
   `ELVProbeWeightPreDot` and `ELVProbeWeightNegativeCap` now identify
   the signed source dot, all inverse powers and normalized pre-cap.
   `ELVReservoirPostUnitCoordinates` and `ELVReservoirPostUnitStandard`
   identify the chosen unit with its canonical dotted append formula.
   `RouquierHomWeightCoordinates` now transports these words through both
   Hom weights, and `Sigma.PaddedBendWordSeries` expands the actual padded
   central map in the same cap/cup words using constructed finite bounds.
   `ELVProbeVacuumBendMonomials.vacuumBendMonomial_native` now identifies
   every evaluated negative-cap/post-unit word, with a strict nonzero
   tensor/odd-coefficient consumer and 41 owned audits.
   `ELVProbeVacuumBendSeries` now sums these words, and
   `ELVProbePaddedVacuumBend.paddedVacuumDx_odd` identifies the actual
   padded entry under its source/target charts; all 41 owned declarations
   and a nonzero asymmetric two-odd consumer pass. Identify prescribed
   inverse rows with polynomial caps and attach all-vector moments and
   bubble normalization. The even moving
   colour's actual shifted probe dot now has `(x-1)^m=0` and is invertible
   in `ELVProbeEvenVacuumPolynomial`; its strict mixed-data/nonzero-source
   consumer audits 16 declarations. `ELVProbeEvenCentralBend`,
   `ELVProbeEvenCentralSlide` and `ELVTensorEvenVacuumCap` now give the
   actual even finite bend, slide, negative-height cap annihilation and
   height-zero principal-cap equality (15/18/27 audited declarations),
   with nonzero odd coefficient inputs in connected mixed data.
   Attach these to the padded chosen inverse, retaining the even signs.
   `ELVTensorVacuumPolynomialWindow` also proves the entire low-unit
   closure window on all vectors (17 audits); actual padded unit-column
   charts are still required to identify the chosen negative inverse row. Generic last-row uniqueness in
   `SwappedVacuum.NegativeCapInverse` does not replace that actual comparison.
   `ELVTensorVacuumWholeInput.tensorSectorInput_eq_supported` now identifies
   the full tensor input with this supported vacuum through both weight
   transports. `ELVTensorVacuumPrincipalFactor` removes both padding charts
   from the chosen height-zero principal isomorphism and retains its exact
   inverse-row formula. The two strict producers and occupied two-odd
   consumer pass, auditing 62 declarations. Evaluate this inverse through
   the same bend charts before applying the polynomial-cap comparison.
5. `SwappedVacuumParameters` now constructs literal highest weights
   `(0,P)` and `(-μ,P)` in the pairing extension, identifies the actual
   probe cutoff with the existing schedule, and proves both factor bounds
   and the coefficient-power window inequality. Its strict mixed,
   repeated-word consumer retains a nonzero common-coroot-kernel coordinate
   and applies actual half-turn injectivity; all 22 declarations are audited.
   `SKM.PairingExtensionDiagrams`, `PairingExtensionPresentation` and
   `QuiverHecke.PairingExtensionAction` now construct the region/signature
   map, transport all defining relations, descend to a linear presentation
   functor and pull back the actual combined upward action, retaining its
   carriers. Strict connected mixed/occupied-probe/coroot-kernel checks
   audit 89 declarations. `PairingExtensionAffine.alpha_map` and
   `PairingExtensionBubbles.homMap_bubAt_betaSYM` now prove the exact
   affine and source-placed normalized bubble squares, including full
   exterior products. `PairingExtensionObservation` transports the action
   and coefficient filtrations; `PairingExtensionPBW` constructs the
   actual affine inverse and full coefficient/PBW equivalence, preserving
   joint degree and both filtrations (nineteen owned audits). Next assess
   the pulled-back-ideal construction proposed above: the final consumer
   needs sufficient observation transport and a lower degree bound, rather
   than an identification with a prescribed original-datum ideal. Prove
   literal composition and generator/ideal comparisons only where a named
   remaining consumer requires them. Forward filtration transport alone
   supplies neither the inverse bound nor the quotient evaluation equation. Restricting the
   factors separately loses the occupied extended coset with second
   coordinate `-P`; only the combined Hom heights cancel this coordinate.
6. Fill `UpwardModuleAction.toSwappedVacuumEvaluation` with the constructed
   action, coefficient and bubble comparisons, bounded corner and exact
   affine evaluation. Apply `nondegeneracy_of_restrictColours_vacuum_evaluations`
   and the existing orientation and ground-ring reductions, followed by the
   checked all-even specialization. This endpoint does not require the
   stronger global relation record in `SwappedVacuumObservation`.

The whole original-weight Hom category can contain other occupied contents
at an absent formal sector. Use the supported category's proved zero
functors for padding; do not infer absence from a weight equality alone.
The intended factor is `elvProbeReservoir`, with its full exterior-coefficient
reservoir and untruncated evaluated OLD probe. `SupportedAction` now supplies
the complete supported upward action. The observation/bubble attachment and
nondegeneracy theorem remain open.

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
| Canonical vacuum class, principal cap and exact quotient transport | [0fe99e8dc4](https://github.com/apellis/odd-lean/commit/0fe99e8dc4520ec9e8174c8e4604c3db181d0378) (complete source tree) | Current unfinished `SupportedTensorVacuumCoefficientClass` producer fails on concrete normalization; `ELVTensorVacuumPrincipalInverse` fails on retained section binders, inverse-square elaboration and final parser alignment. Their consumers are not checked. `ReservoirWordStrictCoherence` and `PairingExtensionPowerIdeal` are untested; `PairingExtensionComposition` fails on the box-product target and tensor-induction API. The unused layer-wrapper attempt is also retained. Restore topical files only; the snapshot is not asserted to build. |
| Vacuum source classes and normalized cap moments | [5c8d834f49](https://github.com/apellis/odd-lean/commit/5c8d834f493e58a278d34090759371b232fa8c3a) (complete source tree) | Proposed canonical vacuum/source-class evaluation, selected tensor input, padded native vacuum bend, chosen principal inverse and polynomial-cap/moment attachment remain incompletely checked. The snapshot also includes separately scoped-checked canonical permutation, supported action and matrix coefficient observation additions awaiting their own full integration. Restore topical files only; this full tree is not asserted to build. |
| Cap windows and canonical tensor observations | [dba1c00c6e](https://github.com/apellis/odd-lean/commit/dba1c00c6e915297859d33d11ec6e8b356feb413) (complete source tree) | Proposed intermediate/positive-height cap and cup identities, finite-column reduction, canonical left-mate normalization, braid-universe attachment, global coefficient/layer observation and finite vacuum-bend comparisons. Strictly checked parts have separate topic evidence; this complete snapshot is not asserted to build. Restore topical files only. |
| Canonical factor cyclicity and tensor observations | [685be86ce9](https://github.com/apellis/odd-lean/commit/685be86ce9e8a3eec9326ea611ce6cec7425e78b) (complete source tree) | Proposed braid-universe attachment, pure distinct-entry coordinates, canonical left-mate cap-pitchfork port, tensor coefficient/word observations and vacuum dot/bend comparisons. This complete snapshot is not asserted to build; restore topical files and consult STATUS for subsequently verified portions. |
| Supported action and vacuum normalization | [490680bf20](https://github.com/apellis/odd-lean/commit/490680bf20173f67e994d0a9c26b3656e6188e06) (complete source tree) | Proposed all-sector inverse, restricted relation, source-polynomial unit, tensor-family and moment-map attachments. The snapshot is not asserted to build; restore topical files only and consult current STATUS for subsequently verified portions. |
| Weighted append tensor/dot/adjunction comparison | `97e4256b` | Historical proposed source, superseded by the full-CI verified tensor/unit and signed-dot formulas (#963) and full-CI verified `ELVWeightedAppendAdjunction` restriction/counit formulas (#972). Double-append crossing, inverse and normalized content/weight transport remain open |
| Scalar probe append tensor/dot comparison | `f145165c357d43b8241de20241cc6e911051f13e` | Historical proposed source; `ELVProbeAppendTensors` now has full-CI verified literal tensor/unit, parity and signed-dot comparison (#963). Chosen adjunction/inverse-matrix transport remains open |

Recover a file with `git show <commit>:<repository-path>`. These preserved source trees are outside the checked library until their
producer and paired consumer checks pass. Reachability is not a verification
claim. Earlier attempts hit normalization/conversion limits; redesign endpoint encodings and reusable comparison
lemmas rather than raising heartbeat or recursion budgets. The shared helper extensions
at the append restart commits have scoped checks only; the integrated #936 source has
its own full-CI boundary and must not be confused with those later extensions.
