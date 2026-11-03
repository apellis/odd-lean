# Independent weight dots in the selected pair coordinates

DeformedActionAssembly §6 (9) needs the independently given weight dots
under the identical comparison used for the supported crossing square.

`elvWeightPairComparison_inner_total` compares induction on the first
weight dot with the right-whiskered single-letter source dot.
`elvWeightPairComparison_outer_total` compares the second weight dot
with the left-whiskered single-letter source dot. Both use exactly
`elvWeightPairComparison` on the actual supported output block.
Neither assumes the desired dot comparison or any inverse matrix.

`ModuleCoordinateSquare` is the literal equality of the entire evaluated
linear maps, kept as a named proposition during specialization.
`ModuleCoordinateSquare_apply` evaluates that equality on every input
vector. It introduces no additional condition. The proof retains the
actual intermediate block instead of replacing it by the canonical
content before specializing the module objects. Generic whole-functor
equality transport then avoids re-elaboration of the large module types.

The producer and paired connected mixed-colour consumer pass strict
checks. Every ordered pair, including repeated even and repeated odd
colours, is instantiated on the actual induced vacuum product. Both
whole-map and all-vector equations are checked; all ten owned declarations
pass the axiom allowlist audit.

Next normalize the two source whiskerings to the positioned source dots
in the checked original-parameter polynomial and assemble the supported
quadratic in these independent weight operators. The absent-predecessor
branch and complete global quadratic and triple fields remain open.
