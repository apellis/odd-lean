# Odd nondegeneracy: mathematical handoff

Start with [STATUS](STATUS.md) for established scope and claim boundaries.
[SwappedNondegeneracy](SwappedNondegeneracy.md) is the proposed written proof.
This file records the next mathematical targets, not session telemetry.

## Dependency order and readiness

| Target | Ready to start? | Existing inputs | Completion criterion / blocker |
| --- | --- | --- | --- |
| Prescribed categorical inverse | Yes: highest-priority risk | Actual short-column squares; `ELVBoundaryRowDivision` and height identity; `ELVCyclotomicAlphaCoordinates.extract_comp_alpha` and `pprime_injective` | Use proved balanced crossing/source coordinates and actual kernel/image data; derive the snake and prescribed augmented inverse, retaining full coefficient twists and all heights |
| Independent content mixed braid | Yes, alongside inverse work | Coherent composition comparisons and independent triple crossing/dot identifications; ordered correction polynomial | Prove the composed independently whiskered braid on these same maps, with parameter twist and equal-colour minus |
| Full-ELV factor family | Partly: construction/comparison work can start | Existing full-ELV content module functors and polynomial relations | Finished family requires the categorical inverse, multicolour relations, naturality and required degree transports; ordinary-polynomial global wrapper does not supply it |
| Whole swapped action | Local comparisons ready; concrete assembly blocked | Conditional assembly; braid from inverse/coefficient inputs; Hom mate and word comparisons | Supply compatible full-ELV factors and concrete crossing/leftward coefficient inputs, then all whole inverse and relation fields |
| Vacuum and bubble recovery | Literal coordinate comparisons ready; final instance blocked | Whole-word Hom crossing; transformed ideal comparisons; abstract signed bounded recovery | Actual action and normalized adjunction must produce its vacuum, corner evaluation and all-height bubble series |
| Final nondegeneracy composition | Blocked on observations | Finite-colour reduction and upward/oriented equivalence are implemented | Construct observations for every finite colour restriction, fixed weight, upward pair and bound; invoke existing consumer |

## First assignment: categorical inverse

Read the top-row, boundary and matrix chain:
[DeformedCyclotomicTopRow](DeformedCyclotomicTopRow.md),
[DeformedMackeyBoundary](DeformedMackeyBoundary.md),
[DeformedBoundaryDivision](DeformedBoundaryDivision.md),
[DeformedRouquierMatrix](DeformedRouquierMatrix.md),
[DeformedMatrixComparison](DeformedMatrixComparison.md).

Use the independently defined `PprimeDomain`, `Source`, `alpha`,
`pprime`, `shortCross` and quotient maps in
`ELVCyclotomicCrossingTensor` / `ELVCyclotomicShortColumns`.
`ELVCyclotomicAlphaCoordinates` proves `extract_comp_alpha`, `alpha_injective`
and `pprime_injective`, with the consumer of the same name; the earlier report
that these were unlocated was an inspection error. `ELVSourceSplitting` now
identifies the source with its prescribed short and polynomial coordinates;
`ELVSourcePolynomialQuotient.sourceQuotientBoundary_eq` identifies the actual odd
induced boundary. Use these committed producers directly. Match the existing actual boundary normal forms to this diagram;
a decomposition using the crossing image is insufficient to identify the
prescribed balanced crossing source. Keep zero corners, height zero, full
exterior coefficients and source/target twists explicit. The immediate output
is the named categorical matrix inverse on these maps, with its required
compatibilities, not another abstract inverse interface.

## Parallel mathematical target: independent braid

Use the existing content composition comparisons and whole associativity,
together with independent single-letter dots and pair crossings. Prove their
composed mixed braid rather than replacing an independently defined operator
by a conjugated one. Retain every intermediate-content cast, ordered polynomial
coefficient, full kernel parity and equal-colour crossing normalization.

## Subsequent synthesis

Build the full-ELV Rouquier/reservoir family and compare its dot with the
proved nilpotent content induction dot. Obtain probe units from its chosen
specialization. Then supply `ProbeReservoir`, coefficient and inverse inputs
for the existing swapped assembly. Use `ELVVacuumWordPairing` for actual
word evaluation before constructing `VacuumCornerEvaluation` and
`AdjunctionBubbleSeries`. The field-linear recovery consumer already exists;
construct its data instead of adding a new equivalent interface.

The proposed cutoff schedule chooses observation bounds, factor cutoffs and
one coefficient truncation before support bounds and terminating-series lengths.
Preserve that dependency order. Do not assume coefficient flatness, evenness of
arbitrary kernels, uniform nilpotence over every weight, or an automorphism
of a finite quotient when only bounded-window substitution is proved.

## Reporting and verification discipline

Update STATUS in place when an obligation closes. Keep this handoff limited
to the current next targets and dependencies; keep PROGRESS as a pointer.
README links here rather than accumulating research checkpoint tables.
Topic notes retain their local arguments and anchors; historical status text
in them is subordinate to STATUS. Previous detailed inventories are in git history.
Record exact declaration names, hypotheses and whether a result is proposed,
implemented, scoped-checked or full-CI verified. Conditional constructors must
list their unconstructed inputs. Do not report workers, sessions or old build
processes as live. Follow AGENTS.md for toolchain, CI and axiom policy.

## Balanced crossing coordinates

`ELVCyclotomicCrossCoordinates` supplies the actual decoder and
`ShortCrossCoordinates.decode_comp_shortCross`, `shortCross_injective`,
`range_shortCross` and `crossingEquiv`. These identify the prescribed short
balanced source with the original crossing span, including full coefficients
and zero Hom corners. The decoder kills the separately proved polynomial
triangular correction. Combine this with `ELVSourcePolynomialQuotient` for
the categorical snake; graded/natural compatibility and augmented inversion
remain open.

## Proposed next constructions under verification

The risk-reduction topic branch contains unverified source drafts and consumers:
`ELVCrossingHeight` (actual crossing injectivity/surjectivity by height and the
zero-height equivalence), `ELVContentWhiskeredMixedBraid` (composed independent
crossings and independent-dot correction), and `ProbeDotPropagation` (ordinary
kernel propagation through same/distinct-colour relations). These are not yet
verified results or concrete full factor/observation instances. The probe note
uses the simpler kernel proof; actual word-corner application remains separate.

## Saved proof drafts and next verification targets

The risk-reduction topic branch preserves these additional UNCHECKED drafts:
`ELVPositiveCrossing`, `ELVBoundarySnake`, `ELVCapCoordinateTransport`,
`ELVCrossingInputDot`, `ELVContentUncorrectedBraid`,
`ELVOffDiagonalLongCoordinates`, and `ProbeWordCorner`.
The corresponding consumers are included where present. The first two are
restricted to diagonal old Hom and odd moving colour. Cap transport constructs
input-oriented contraction/dot descent with the polynomial defect retained;
its identification with the actual categorical dotted counit remains open.
The off-diagonal coordinate draft still takes an old normal-form index: canonical
choice independence and the empty-index case remain to be completed.
ProbeWordCorner is an unfinished transport into the actual cyclotomic eAe corner.

Only `ProbeDotPropagation` and its concrete consumer have passed scoped checks
in this continuation; its independent PR is #751 and full CI remains required.
The other new constructions must be elaborated, corrected, consumed and audited
before being recorded as verified. Build their named module targets, then their
NonVacuity targets. The negative cap matrix, off-diagonal/naturality extension,
full factor/action and actual observations remain the critical chain.

## Proposed off-diagonal long coordinates

`ELVOffDiagonalLongCoordinates` extends long extraction and explicit finite
sections to full old Homs `Old(v,t)`. Intermediate constructions use an old
normal-form index; the proposed final maps remove it using choice-independence
and the proved zero Hom in the empty-index case. Same/off-exponent readback,
finite support, split surjectivity and section injectivity are drafted with
concrete connected all-odd off-diagonal and empty-Hom consumers. These latest
extensions remain unchecked until CI. Exact relative-short kernel and
boundary/leading-map transport are subsequent obligations; no full factor
inverse or nondegeneracy instance is claimed.
