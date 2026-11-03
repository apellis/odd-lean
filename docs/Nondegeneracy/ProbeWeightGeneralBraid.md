# The general probe braid

Brundan–Ellis (1.9), outside the repeated-outer-colour correction case,
is attached to the independently chosen probe weight generators in
`ELVProbeWeightGeneralBraid`.

At an occupied output block, the six maps in the two crossing paths are
identified by `probeOldWeightCrossPrefix_via_total` and
`probeOldWeightCrossSuffix_via_total` with the prescribed crossings in a
single stored append cube. Each vertex retains its own canonical word.
The six coordinate changes cancel pairwise; the remaining equality is
`probeStoredBraid` for the scalar-evaluated OLD modules. The cancellation
and scalar linearity of the one or two mapped crossings are proved in
abstract categories before substitution of the prescribed module functors. The three
normalizing signs are retained independently, including equal-colour
pairs. The acting parameters are `parameterTwist D Sc`; the presentation
parameters are `Sc`.

`probeOldWeightGeneralBraid_component` states the occupied-coordinate
equation. `probeOldActionCross_generalBraid` includes every output
coordinate: when no three-step predecessor exists, the actual source
object is zero. `probeOldRouquierData_generalBraid` is the named
`rouquierMulticolourBraidEquation` for the chosen generator data. None of
these statements assumes a crossing comparison or braid relation.

The paired consumer includes both mixed and asymmetric data, all-equal
and partially repeated triples, and nonzero admissible interior
parameters. The corrected repeated-outer equation belongs to the
separate mixed-braid attachment.
