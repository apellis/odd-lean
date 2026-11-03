# The selected pair comparison under OLD representative changes

The crossing and inverse relations in Brundan–Ellis (1.7)–(1.8),
(1.12)–(1.14) involve two successive append inductions. Their
representative comparison must use the same lower and upper adjunction
comparisons as the local generators.

Let `e₁ : Ind J ⋙ R₁ ≅ R₀ ⋙ Ind K` and
`e₂ : Ind L ⋙ R₂ ≅ R₁ ⋙ Ind M` be the specified single-append
comparisons. `oldAppendPairReindexIso` is `Ind J` whiskered with `e₂`,
followed by `e₁` whiskered with `Ind M`. Its component first applies
`e₂` to the induced input module and then induces the component of `e₁`.
There is no independently chosen pair comparison.

The upper comparison sends `[g ⊗ [a ⊗ b]]` to the same outer tensor
with its upper source reindexed. The induced even lower comparison acts
on the inner vector without a twist. Its single-append tensor formula
then gives the same `g`, `a`, and `b` at their reindexed source objects.
Both coefficient arrows and the vector may be inhomogeneous.

The comparison is the input for the chosen pair-crossing square. The
crossing square, its mate square, and the canonical local and distinct
inverse records are subsequent obligations.

`oldAppendPairReindexIso_hom` identifies the chosen composite component;
`oldAppendPairReindexIso_hom_mem` proves its evenness.
`oldAppendPairReindexLinear_comp` and
`oldAppendPairReindexIso_hom_tensor` give the linear factorization and
nested tensor formula. `probeAppendPairReindexIso` restricts the same
comparison to the full evaluated probe categories, retaining the given
forward and inverse maps and the forward tensor map literally.

The producer and paired consumer pass strict scoped checks with warnings
as errors and both compatibility settings. The consumer uses connected
even/odd data, regular probe modules, a nontrivial base permutation and
canonical upper representatives. It checks the nested formula for
arbitrary colours, arrows and coefficient vectors, the evaluated native
maps, forward evenness and odd-input naturality. Its axiom audit covers
all 67 owned declarations. Full integration verification remains separate.
