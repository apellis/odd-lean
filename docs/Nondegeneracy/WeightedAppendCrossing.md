# Weighted equal-colour crossing comparison

DeformedActionAssembly §5 and DeformedMatrixComparison (2), (4) require the
chosen equal-colour crossing rather than an unspecified homogeneous map.
`truncatedEqualCrossComponent` is the literal quotient of the old last-two-strands
crossing. `oldTruncateFunctor_map_equalCross` proves this equality directly;
`truncatedEqualCrossComponent_heq` identifies it with the existing
`truncatedAppendComponent (crossTwo i i)` under word associativity.
`truncatedEqualCross_supernatural` retains the full coefficient parity.

`pairWeightedModuleIso_hom_crossing` proves that the selected five-map pair
comparison intertwines the prescribed crossings on composed induction.
`pairWeightedModuleIso_hom_signedCrossing` retains the action's extra minus.
The formulas hold on whole coends, with arbitrary coefficient arrows and vectors.

The paired consumer uses the connected mixed-parity datum, its truncated
representable, both moving colours, the odd crossing sign, and the vacuum
representable. These results compare composed induction. Attaching both
canonical induction flattenings and the ordinary-adjunction mate remains a
separate obligation for the iterated matrix crossing.
