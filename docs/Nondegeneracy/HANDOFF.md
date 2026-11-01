# Odd nondegeneracy: mathematical handoff

Start with [STATUS](STATUS.md) for established scope and claim boundaries.
[SwappedNondegeneracy](SwappedNondegeneracy.md) is the proposed written proof.
This file records the next mathematical targets, not session telemetry.

## Dependency order and readiness

| Target | Ready to start? | Existing inputs | Completion criterion / blocker |
| --- | --- | --- | --- |
| Prescribed categorical inverse | Diagonal construction ready; full action has prerequisites | Actual short-column squares; `ELVBoundaryRowDivision` and height identity; `ELVCyclotomicAlphaCoordinates.extract_comp_alpha` and `pprime_injective` | Use verified diagonal raw negative matrix (#777) and height consequences (#760); check the positive matrix, then extend arbitrary-Hom boundary leading terms, division and cap pivots. No diagonal-to-all-representables reduction is proved; retain full twists and all heights |
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

## Probe factors

`ProbeDotPropagation` and `ProbeWordCorner` are integrated after full CI
in #751 and #752. Use the actual corner map and its nilHecke relations.
`ProbeWordEntries` adds actual rectangular entries, their word supports,
target-row cancellation by corner units, and the distinct-kernel criterion;
source and consumer passed full CI in #756. Supply its actual distinct-colour slide,
ordered quadratic, and unit leading corner term next. A word-corner unit
is not a left-regular element of the entire algebra.

Cofinal first-dot probe powers and monochromatic all-position injectivity are
verified in #754. Dimension-free monochromatic all-position units are verified in #768.
Actual distinct-colour unit transport and mixed-word induction remain under
verification.
For finite dimension use raw finite append spanning and ordinary coefficient
specialization; positive-weight coefficient truncation cannot specialize to
nonnilpotent binomial constants.

## Quantifiers and arbitrary endpoints

Two prerequisites must remain explicit during synthesis.

* Boundary division and the current augmented matrix use diagonal old
  endomorphism coefficients. The full module action needs arbitrary
  `Old(v,t)`. Extend the actual long extraction/short-kernel factorization,
  prove output-arrow covariance, and reuse the diagonal leading polynomial
  by composition with arbitrary old morphisms. General module division and
  cap pivots must then be checked; do not infer them from diagonal inverses.
* Nilpotence of the actual induced dot is per target-content block. Build
  denominator units componentwise and assemble their even natural inverse.
  Do not assume a common exponent over all contents in one weight fibre.
  The old strong nilpotence constructor may remain as a sufficient corollary.

The actual old-module parity/canonical J and whole-counit comparisons are
under verification. Keep their complete output twist and higher-row signs;
a raw cap row is not yet an identified categorical counit.

## Checked height and dot inputs

`ELVCrossingHeight` (#760) supplies the actual diagonal crossing's height
injectivity/surjectivity and zero-height equivalence. Its raw negative matrix, actual snake and dotted input contractions are
verified in #777, including height zero. The raw positive matrix is checked
separately in #776. These diagonal odd-colour results are not categorical
factor inverses on all old morphisms.

`ELVWeightDot` (#772) supplies the actual normalized weight dot and its
per-content nilpotence. That bound is now strengthened in #778: a single exponent at each fixed
target-content block works for every input module. Actual adjunction
transpose transport is the next construction. This still permits different exponents at different contents.
Use direct probe units (#768) rather than requiring finite dimension solely
to turn same-colour injectivity into a unit. Raw append spanning (#766)
remains a verified independent specialization input.
