# Iterated weighted append comparison

The selected pair comparison acts on induction along composed append functors.
DeformedActionAssembly §5 and DeformedMatrixComparison (2), (4) need the
iterated induction modules supporting the signed equal-colour crossing.

`doubleInduced_killsWeightedCoefficients` proves the exact full coefficient
annihilator after both inductions. `weightedInductionFlattening` descends the
existing old induction-composition isomorphism, with its selected hom and
inverse. `weightedModuleHom_mem` and `weightedInductionFlattening_hom_mem`
retain parity under this descent.

`doubleWeightedModuleIso` composes that descended flattening, the selected
`pairWeightedModuleIso`, and the inverse truncated induction flattening.
`doubleWeightedModuleIso_flatten` proves the exact resulting coherence square
on the given module morphisms. The paired consumer instantiates both inverse
products and this square on the mixed-parity and vacuum representables.

The explicit nested tensor formula and the signed crossing/mate comparison
on this iterated isomorphism remain to be attached; the existing signed pair
crossing comparison concerns composed induction.
