# Odd nondegeneracy: mathematical handoff

Start with [STATUS](STATUS.md) for established scope and claim boundaries.
[SwappedNondegeneracy](SwappedNondegeneracy.md) is the proposed written proof.
This file records the next mathematical targets, not session telemetry.

## Dependency order and readiness

| Target | Ready to start? | Existing inputs | Completion criterion / blocker |
| --- | --- | --- | --- |
| Prescribed categorical inverse | Diagonal construction ready; full action has prerequisites | Actual short-column squares; `ELVBoundaryRowDivision` and height identity; `ELVCyclotomicAlphaCoordinates.extract_comp_alpha` and `pprime_injective` | Use verified diagonal raw negative matrix (#777) and height consequences (#760); check the positive matrix, use verified arbitrary-Hom long coordinates (#753), then use the verified exact short kernel (#764), then finish boundary leading terms, division and cap pivots. No diagonal-to-all-representables reduction is proved; retain full twists and all heights |
| Even-moving full-ELV inverse | Separate action prerequisite | Generic coordinates and repeated-even norm recursion; ordinary-polynomial global wrapper is conditional | Prove the even-moving boundary leading/division and categorical matrix with all other colours’ exterior coefficients retained; do not regard the full superalgebra as a commutative scalar ring |
| Independent content mixed braid | Yes, alongside inverse work | Coherent composition comparisons and independent triple crossing/dot identifications; ordered correction polynomial | Prove the composed independently whiskered braid on these same maps, with parameter twist and equal-colour minus |
| Full-ELV factor family | Actual categories and adjunction verified; inverse assembly blocked | Canonical content parity and actual weight E/F adjunction (#755, #757), full-ELV polynomial relations | Finished family requires the categorical inverse, multicolour relations, naturality and required degree transports; ordinary-polynomial global wrapper does not supply it |
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
compatibilities. The canonical old induction/representable comparison is
verified in #806 and supplies its actual upper-Hom target coordinates.

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

## Joint coefficient and strand detection

This input is full-CI verified. `ELVCoefficientWindowTensor` (#812)
uses affine PBW freeness to retain bounded polynomial/exterior coefficients.
`ELVJointPBWDetection` (#819) combines that injection with the actual
truncated-kernel degree bound. `ELVBoundedSourceDetection` (#820)
embeds the exact bounded-recovery `ExtendedAtMost` window into one such
joint window, with bounds fixed before the cutoffs, and proves that the
actual quotients jointly separate every source Hom for finite colours.

Next connect these maps to the normalized action and vacuum coordinates.
The actual weighted module/map/isomorphism descent is verified in #825;
show old induction preserves this annihilator class and compare the induced
module and adjunction with the existing truncated construction.
The weighted coefficient ideal contains odd generators; no even-powers
replacement was used. A quotient must preserve the action and its
prescribed inverse, not merely append maps. Binomial probe specialization
belongs to the untruncated old category and is a separate construction.

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

## Probe factors

The dimension-free unit stack is full-CI verified in #807: actual signed
slides and ordered quadratic identities yield units at every mixed-word
position, and these give signed induction-dot isomorphisms at all heights,
including vacuum, on the existing content and weight categories.

Canonical binomial specialization is verified in #813, and its original
cyclotomic ideal descent, identity/composition and append compatibility in
#814. Next extend these Hom maps to the existing content algebras and module
action, retaining the exact prescribed dots, adjunction and inverse matrices.
Scalar specialization is not faithful on the full coefficient algebra;
source coefficient detection belongs to the separate reservoir.

For finite dimension use raw finite append spanning and ordinary coefficient
specialization; positive-weight coefficient truncation cannot specialize to
nonnilpotent binomial constants.

## Quantifiers and arbitrary endpoints

Two prerequisites must remain explicit during synthesis.

* Boundary division and the current augmented matrix use diagonal old
  endomorphism coefficients. The full module action needs arbitrary
  `Old(v,t)`. Use verified arbitrary-Hom long extraction/section (#753) and output-arrow
  covariance (#779); use the verified exact short kernel (#764) and reuse the diagonal leading polynomial
  by composition with arbitrary old morphisms. General module division and
  cap pivots must then be checked; do not infer them from diagonal inverses.
* Nilpotence of the actual induced dot is per target-content block. Use verified componentwise denominator units and their even natural inverse
  (#794), together with concrete dot commutation and parity-shift transport (#801).
  Do not assume a common exponent over all contents in one weight fibre.
  The old strong nilpotence constructor may remain as a sufficient corollary.

The old-module parity and whole-counit comparison is verified in #761;
canonical J, its induced source comparison and the categorical higher rows
remain under verification. The standalone odd-dot cap-sign identity is
verified in #803. Keep their complete output twist and higher-row signs;
a raw cap row is not yet an identified categorical counit.

## Checked height and dot inputs

`ELVCrossingHeight` (#760) supplies the actual diagonal crossing's height
injectivity/surjectivity and zero-height equivalence. Its raw negative matrix, actual snake and dotted input contractions are
verified in #777, including height zero. The raw positive matrix in #776 remains under verification. These diagonal odd-colour results are not categorical
factor inverses on all old morphisms.

`ELVWeightDot` (#772) supplies the actual normalized weight dot and its
per-content nilpotence. That bound is now strengthened in #778: a single exponent at each fixed
target-content block works for every input module. Actual adjunction
transpose transport is verified in #790; derive its concrete norm units next. This still permits different exponents at different contents.
Use all-position mixed-word probe units (#807) without a finite-dimensionality premise. Raw append spanning (#766)
remains a verified independent specialization input.
