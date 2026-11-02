# Ordinary adjunction through weighted append comparison

For DeformedActionAssembly §§5–6 and STATUS critical-chain item 2,
`weightedAppendRestrictionIso` in `ELVWeightedAppendAdjunction` compares
pullback of truncated restriction with old restriction of pullback by
identity vector maps. `weightedAppendRestrictionNaturalIso` assembles these
components with naturality for arbitrary supernatural input-module maps.

`restrictionCounitLinear` realizes the actual ordinary counit on the
literal coend of the restricted module, with its exact tensor formula.
`appendWeightedModuleIso_hom_counit` identifies this old counit, after the
even degree-zero induction component of the restriction-square comparison,
with the truncated counit after `weightedAppendComparisonLinear`. The equality holds
on all coend vectors and arbitrary output words. Its proof applies the
literal tensor formula and evaluates both prescribed counits; neither
counit nor the append comparison is replaced by a newly chosen map.

The companion unit formula is `appendWeightedModuleIso_hom_unit` in
`ELVWeightedAppendTensors`. Normalized content and weight functor assembly
remain separate.

The paired mixed-representable consumer checks inverse products, evenness,
input-map naturality, whole restriction-square isomorphism and the exact
counit equality for both moving parities. It audits all owned declarations.
The producer and paired consumer pass strict scoped compilation with the
pinned toolchain and both compatibility settings; all 26 owned declarations
have allowed axioms. Full CI remains pending.
