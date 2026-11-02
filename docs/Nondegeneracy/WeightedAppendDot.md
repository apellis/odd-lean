# Dot transport through weighted append comparison

For DeformedActionAssembly §§5–6 and STATUS critical-chain item 2,
`appendWeightedModuleIso_hom_dot` in `ELVWeightedAppendDot` applies the whole
tensor formula of `ELVWeightedAppendTensors` to the prescribed signed old
coend dot. The quotient sends the old appended dot to the literal truncated
dot and preserves the full parity twist. The selected comparison therefore
intertwines these operators on every vector of every old output word.

The dot is `CyclotomicCrossingTensor.actualInductionDot` on the unchanged
old coend values, and `moduleInductionDot` on truncated induction. This
comparison does not yet bundle the old operator as a transformation of the
descended functor or assemble the normalized content/weight dot.

The mixed-representable consumer uses a connected datum with one even and
one odd colour. It checks the component equality, evaluation on arbitrary
vectors, the quotient of the exact old dot and its negative odd twist.
All owned declarations are audited. The statements are proposed until
strict scoped compilation and the paired consumer pass; full CI is separate.
