# Canonical quotient comparison for two appended strands

The equal-colour crossing and mate transport in DeformedActionAssembly §5
and DeformedMatrixComparison (2), (4) uses the existing old double-append
crossing and its canonical induction flattening. The quotient comparison
must preserve the complete coefficient algebra and the selected maps.

`pairAppend_oldCoefficientBasis` and `pairAppend_truncate` retain the
literal coefficient basis and the strict quotient square for `J_i ⋙ J_j`
and `T_i ⋙ T_j`, with no word reassociation. The weighted coefficient
annihilator is preserved by induction along that composed append functor;
odd coefficient generators are included.

`pairWeightedModuleIso` consists of the same five quotient/composition
isomorphisms as the one-letter comparison, now applied to the two
composed append functors. Both directions are even. Its raw realization
`pairAppendComparisonLinear` sends every `[g ⊗ b]` to `[Q(g) ⊗ b]`.
There is no flatness premise or homogeneity restriction on these factors.

The paired consumer uses a connected datum with one even and one odd
colour, equal and distinct pairs, an odd coefficient, mixed and vacuum
representables, and both inverse products. The producer and paired consumer
pass strict scoped compilation with the pinned toolchain and compatibility
settings; all 59 owned declarations have allowed axioms. Full CI is pending.
Naturality in the input module, comparison with iterated induction,
flattening coherence and prescribed equal-colour crossing transport remain
separate next obligations.
