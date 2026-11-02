# Dot transport through weighted append comparison

For DeformedActionAssembly §§5–6 and STATUS critical-chain item 2,
`appendWeightedModuleIso_hom_dot` in `ELVWeightedAppendDot` applies the whole
tensor formula of `ELVWeightedAppendTensors` to the prescribed signed old
coend dot. The quotient sends the old appended dot to the literal truncated
dot and preserves the full parity twist. The selected comparison therefore
intertwines these operators on every vector of every old output word.

The old dot is `CyclotomicCrossingTensor.actualInductionDot` on the
unchanged old coend values. The target is the literal `transformLinear`
for the truncated appended dot component, underlying `moduleInductionDot`.
The comparison is `weightedAppendComparisonLinear`, the selected module
isomorphism on those raw coend values. This
comparison does not yet bundle the old operator as a transformation of the
descended functor or assemble the normalized content/weight dot.

The mixed-representable consumer uses a connected datum with one even and
one odd colour. It checks the component equality, evaluation on arbitrary
vectors, the quotient of the exact old dot and its negative odd twist.
The producer and paired consumer pass strict scoped compilation with the
pinned toolchain and compatibility settings. All 11 owned declarations
have allowed axioms. Full CI remains pending.
