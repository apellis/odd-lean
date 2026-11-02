# Odd nondegeneracy: mathematical handoff

Start with [STATUS](STATUS.md) for established scope and claim boundaries.
[SwappedNondegeneracy](SwappedNondegeneracy.md) is the proposed written proof.
This file records next mathematical dependencies, not session telemetry.

## Dependency order and readiness

| Target | Ready to start? | Established inputs | Completion criterion / blocker |
| --- | --- | --- | --- |
| Fixed-content/weight matrix inverse assembly | Arbitrary-module component inverses full-CI verified in #951/#952 | Target-fixed coefficient bijectivity, balanced tensor transfer, exact forward identities and even inverse | Assemble natural isomorphisms on the actual content and weight functors; compare chosen generators and adjunction maps |
| Independent content braid | Whole corrected polynomial lift and independent three-dot families implemented; original exact heads full-CI verified (#933/#934) | Canonical carriers/slides, prefix/suffix crossing families, corrected component relation and `contentMixedBraidTransform` | Transfer the content relations to weight functors; finish pair/triple whiskering comparisons (global crossing and whole canonical pair coherence scoped-checked; full CI pending) |
| Old/truncated action comparison | Pointwise append module isomorphism verified | Weighted module descent (#825), quotient-induction counit module isomorphism (#835), induction preservation and append comparison (#840) | Input-module naturality is verified in #868; finish chosen dot/crossing/adjunction transport, then exact content and weight assembly |
| Full-ELV factor family | Categories, adjunction and old-module component inverses verified; content/weight relation assembly remains open | Content parity (#755), weight E/F and adjunction (#757, #781), polynomial relations | Content/weight inverse assembly, composed braid, naturality and degree transports; compare algebra parameters with parameterTwist Sc |
| Concrete swapped action | Generic denominator interfaces verified; instantiation has prerequisites | Blockwise transpose (#790), transposed norm units (#811), inverse-unit mate criteria (#817), weak Sigma source-norm interface (#834), actual module-category universes (#861), all-position probe units (#807) | Even and odd literal source norms verified (#844/#882); prescribed coefficients, compatible factors, crossing coefficients and whole inverse/relation fields |
| Vacuum and bubble recovery | Coordinate comparisons ready; final instance blocked | Joint full-coefficient source detection (#812, #819, #820), whole-word evaluation, abstract signed bounded recovery | Actual action and normalized adjunction must produce its vacuum, corner evaluation, all-height bubble series and bounded recovery identity |
| Final nondegeneracy | Blocked on observations | Finite-colour reduction, upward/oriented equivalence and observation consumer | Construct observations for every finite colour restriction, original weight, upward pair and bound |

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
[full CI](https://github.com/apellis/odd-lean/actions/runs/41489136665). Assemble these summand maps into the finite-family source/target
functors and prove whole-matrix input-module naturality, then use the
existing output-content component inverses. The entry families alone do
not yet give a natural isomorphism in the input module.

Next compare these natural isomorphisms with the actual fixed-content functors,
then transfer to original-weight functors. Keep the target-fixed count,
chosen source parity coordinates and literal ordinary unit/cap entries.
Prove compatibility with the selected dot, crossing and adjunction maps
before using these inverses in a full-ELV factor action. The component
isomorphisms alone do not supply that action.

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
consumers; full CI remains pending. The crossing retains the prescribed
equal-colour normalization and the zero coordinates without a double
predecessor. Pair/triple whiskering relation transfer and the full factor
action remain open. Retain intermediate-content transports, ordered polynomial
coefficients and full kernel parity.

A full-ELV factor family still requires the categorical inverse, these
multicolour relations and their naturality. Its distinct-colour factor mate
inverse (Brundan--Ellis (1.12)) is a separate open construction: formalize
`DeformedActionAssembly` sections 2--4, including the distinct outer-colour
ideal identity, crossing-coset PBW inverse and literal cup-crossing-cap
comparison. Existing ordinary-polynomial mate formulas and swapped raw
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
#938/#940/#936, with original full CI. Finish the literal scalar/weighted unit
specializations and chosen
dot/crossing/adjunction compatibility, then content/weight transport.

Keep the literal weighted coefficient ideal, including all odd generators.
No even-powers replacement is justified. A quotient must preserve the action
and its prescribed inverse, not merely append maps.

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
unit-tensor formula are full-CI verified and integrated in #897. Finish their whole
generator formula and the exact dot, adjunction and inverse-matrix
comparison. The signed ordinary induction-dot unit is full-CI verified in
#893. The prescribed signed dot on the actual old append coend is also a
unit for scalar-evaluated modules, with the canonical probe specialization
full-CI verified and integrated in #927. Neither result requires finite
dimension or a coend-comparison premise. The selected ordinary model and
its exact generator/adjunction transport remain required.

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
They are full-CI verified and integrated through #949; the raw even mate remains unfinished.
Finish the remaining literal
CrossCoeff input assembly. Do not assume a common exponent over
all contents or add another conditional factor-family wrapper.

## Final synthesis and verification

`SwappedVacuum/InverseCapMoments` is scoped-checked with occupied level-one
and degree-two concrete consumers and an owned-declaration axiom audit.
Its signed recurrence derives the principal cap and all positive-index
right moments from the slide, probe polynomial and coefficient-extraction
window. Attach the latter window and the literal inverse maps to the
actual vacuum; no actual bubble-series interface is instantiated yet.
See [InverseCapMoments](InverseCapMoments.md). Its source head
`532683e2db4770b22950a5356863935e9c1d8851` passed
[full CI](https://github.com/apellis/odd-lean/actions/runs/41522225499) and
is integrated in #955.

`SwappedVacuum/NegativeCapMoments` now proves the negative-height
annihilation and low-unit window tests from the same signed slide and
probe polynomial. Its concrete occupied level-two/probe-level-one consumer
identifies the polynomial candidate with the final row of a nontrivial
whole augmented inverse. Strict local checks and the owned audit pass;
full CI is pending. Next attach these tests to the actual module matrices,
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
| Weighted append tensor/dot/adjunction comparison | `97e4256b` | Proposed literal tensor, dot and restriction/counit comparison sources; producer and consumer checks remain open. The shared induction-square helper has separate scoped checks |
| Scalar probe append tensor/dot comparison | `f145165c357d43b8241de20241cc6e911051f13e` | Proposed literal whole generator and signed-dot transport; source endpoint conversion and paired consumer remain unverified |
| Raw even mixed mate and coefficient comparison | `159914dd525f8caca2d979cb068ecdcfedc095f6` | Proposed literal componentwise source norm, even mate, coefficient uniqueness and parity-unified attachment; both producer/consumer pairs remain unverified |
| Input-module finite matrix assembly | `532b47927d45c384e4a6af1ed9cd57dfcdcb05ee` | Generic finite product maps are scoped-checked; whole input-module naturality and content functor inverse sources and their consumers remain unverified |
| Actual vacuum coefficient functional | `658f64966768431d4d6a3011496546061e89bce2` | Proposed inverse-row extraction, literal dot/unit window and exterior naturality on the old vacuum; concrete producer/consumer checks and final weighted/swapped attachment remain open |
| Global weight crossing comparison | `cd6341f610847f5a72b92a7b20c8c09061da0593` | Proposed whole crossings and pair comparison; the first producer has a scoped check, while this preserved combined source does not establish the consumer or second comparison |

Recover a file with `git show <commit>:<repository-path>`. These preserved source trees are outside the checked library until their
producer and paired consumer checks pass. Reachability is not a verification
claim. Earlier attempts hit normalization/conversion limits; redesign endpoint encodings and reusable comparison
lemmas rather than raising heartbeat or recursion budgets. The shared helper extensions
at the append restart commits have scoped checks only; the integrated #936 source has
its own full-CI boundary and must not be confused with those later extensions.
