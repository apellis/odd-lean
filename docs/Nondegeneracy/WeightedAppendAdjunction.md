# Ordinary adjunction through weighted append comparison

For DeformedActionAssembly §§5–6 and STATUS critical-chain item 2,
`weightedAppendRestrictionIso` in `ELVWeightedAppendAdjunction` compares
pullback of truncated restriction with old restriction of pullback by
identity vector maps. `weightedAppendRestrictionNaturalIso` assembles these
components with naturality for arbitrary supernatural input-module maps.

`appendWeightedModuleIso_hom_counit` identifies the actual ordinary old
counit, after induction of the restriction-square comparison, with the
truncated counit after the chosen append comparison. The equality holds
on all coend vectors and arbitrary output words. Its proof applies the
literal tensor formula and evaluates both prescribed counits; neither
counit nor the append comparison is replaced by a newly chosen map.

The companion unit formula is `appendWeightedModuleIso_hom_unit` in
`ELVWeightedAppendTensors`. Normalized content and weight functor assembly
remain separate.

The paired mixed-representable consumer checks inverse products, evenness,
input-map naturality, whole restriction-square isomorphism and the exact
counit equality for both moving parities. It audits all owned declarations.
These formulas are proposed until strict scoped compilation and the paired
consumer pass; full CI remains separate.
