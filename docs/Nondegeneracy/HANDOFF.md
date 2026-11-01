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

## Proposed parity structure on full-ELV module categories

`ELVContentParity` constructs the parity shift of the existing
`ContentModules` by postcomposition with vector parity and the whiskered odd
isomorphism. This is the Pi-supercategory prerequisite for the full-ELV factor
weight objects; it needs no local inverse or ordinary-polynomial replacement.
Its production file and concrete asymmetric vacuum consumer are proposed and
await full CI; no completed factor or global weight-family construction is claimed.

## Canonical module parity and the actual counit

Candidate source modules `ELVContentParity`, `ELVInductionParityComparison`
and `ELVOldSupermodules` construct the module parity operation, its canonical
transport through actual balanced induction, the whole counit comparison,
and actual representable supermodules on the existing old quotient category.
These terms await their full CI gate; they are not a completed factor action.

The next specialization identifies `CyclotomicCrossingTensor.coefficient 1`
with the parity-shifted restriction of the old representable. Retain the
existing coend, full coefficient parity, independently defined counit and
all target arrows. Then transport through coefficient truncation and exact
content, and compare actual dotted counits with the already specified
input contraction rows. Neither ordinary-polynomial factors nor an
unspecified kernel isomorphism supplies this comparison.
