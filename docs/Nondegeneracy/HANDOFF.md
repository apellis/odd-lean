# Odd nondegeneracy: mathematical handoff

Start with [STATUS](STATUS.md) for established scope and claim boundaries.
[SwappedNondegeneracy](SwappedNondegeneracy.md) is the proposed written proof.
This file records next mathematical dependencies, not session telemetry.

## Dependency order and readiness

| Target | Ready to start? | Established inputs | Completion criterion / blocker |
| --- | --- | --- | --- |
| Arbitrary-module categorical inverse | Representable component inverses verified; kernel transfer has explicit prerequisites | All four actual component inverses (#889), generic arbitrary-module kernel tensor (#878) | Finish concrete graded kernel matrices, coend realizations, finite SVec assembly and fixed-content inclusion/extension bridge; then prove arbitrary-module bijectivity |
| Independent content braid | Ready alongside inverse work | Canonical carriers and independent triple maps (#832), distinct slides (#836), coherent composition comparisons | Prove composed independently whiskered braid on the same maps, with ordered correction polynomial, parameter twist and equal-colour minus |
| Old/truncated action comparison | Pointwise append module isomorphism verified | Weighted module descent (#825), quotient-induction counit module isomorphism (#835), induction preservation and append comparison (#840) | Input-module naturality is verified in #868; finish chosen dot/crossing/adjunction transport, then exact content and weight assembly |
| Full-ELV factor family | Categories and adjunction verified; inverse and relation assembly blocked | Content parity (#755), weight E/F and adjunction (#757, #781), polynomial relations | Categorical inverse, composed braid, naturality and degree transports; compare algebra parameters with parameterTwist Sc |
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
self-colour leading unit. These are representable component inverses;
arbitrary-module inversion is still a separate obligation.

### Arbitrary-module kernel transfer

The generic coefficient-kernel tensor isomorphism is verified (#878).
Finite kernel products are verified in #890. Concrete Hom-kernel and IndRes
realizations and grading are scoped-checked in #883/#886/#888/#904 and
successor branches; they still need full CI. The actual finite SVec maps and even inverses are scoped-checked
in #896. The fixed-content counts in #900/#903 use the exact content height
Q−S, so one finite count applies throughout each block. It is not a constant
on the entire old category.

The actual ordinary-right kernel maps are scoped-checked in #911 and their
entry evaluation on arbitrary supermodules in #915. Prove their pointwise
bijectivity using these fixed-content inverses and the off-content zero
lemma, scoped-checked in #914. With the count fixed by target content,
matching source content uses the representable inverse and every other
source component is zero. Keep the literal action
a ↦ precomposition by a, with its verified tensor covariance; it must not be
silently identified with a supernatural representing map that includes
projection and twist. Tensor the resulting kernel isomorphism with an
arbitrary input module, and identify both endpoints with the actual action
modules, including grading, shifts and finite sums.

A direct whole-old-category kernel with target-fixed count is available
once matching-content inversion and off-content vanishing are combined.
Its arbitrary-module matrix evenness is already scoped-checked in #896;
underlying kernel-tensor bijectivity then gives an even inverse. Separately,
the concrete factor action uses fixed-content module categories, while the
old induction coend ranges over the entire old category, so its content
action realization still needs an explicit comparison. Fully faithful induction along the content inclusion recovers the original
module after restriction in the scoped-checked #909; its append comparison
must agree with the chosen action. Do not assume
an equivalence between content modules and arbitrary modules on the entire
old category.

Keep arbitrary old endpoints, empty Hom corners, height zero, full exterior
coefficients and source/target twists explicit. Other colours' exterior
coefficients are not a commutative ground ring.

## Independent braid and factor assembly

Use existing whole associativity and independent single-letter dots and pair
crossings. Canonical carriers and foundational relations are verified in
#832, distinct slides in #836. The composed prefix, corrected and uncorrected component braids and natural
crossing families are scoped-checked in #892/#894/#899/#901/#906. Full CI,
whole-transformation relations and weight assembly remain open. Retain intermediate-content transports, ordered polynomial
coefficients, full kernel parity and equal-colour crossing normalization.

A full-ELV factor family still requires the categorical inverse, these
multicolour relations and their naturality. The older ordinary-polynomial
global constructor assumes local inversions and does not construct the
full exterior-coefficient family. The written pairing extension and balanced
cutoff schedule preserve the original weight realization; supplied CScalars,
its extension and the action restriction are verified in #864. This includes
parameterTwist compatibility and every RouquierMulticolour restriction field;
the construction still needs the concrete extended factor family.

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
isomorphic to truncated append induction (#840). Input-module naturality for every supernatural module map is verified in #868. Finish chosen
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
unit-tensor formula are scoped-checked in #885/#897. Finish their whole
generator formula and the exact dot, adjunction and inverse-matrix
comparison. The signed ordinary induction-dot unit is full-CI verified in
#893; no finite-dimensionality premise is needed for that unit.

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
isomorphisms and coefficient parity are scoped-checked in #913/#917/#919.
Finish their full-package integration and the remaining literal
CrossCoeff input assembly. Do not assume a common exponent over
all contents or add another conditional factor-family wrapper.

## Final synthesis and verification

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
