# Homogeneous distinct mate isomorphism

This packages the arbitrary-module inverse of
[DistinctModuleInverse](DistinctModuleInverse.md) in the two forms needed
by Brundan–Ellis (1.12): an old-module isomorphism at each input module,
and a supernatural isomorphism of the two induction–restriction functors.
The forward map in both forms is the chosen rectangular mate, whose
crossing is positive and has parity `p(i)p(j)`.

For general superfunctors `F,G`, `HomogeneousSuperfunctorIso.inverseSupernatural`
starts with a family of isomorphisms `e_X : F(X) ≅ G(X)` whose forward
maps are supernatural of parity `p`. Inverse maps have parity `p` by
inverse homogeneity. Apply forward naturality to `twist_p(f)` and use
`twist_p(twist_p(f)) = f`; cancellation then gives

    G(f) ≫ e_Y⁻¹ = e_X⁻¹ ≫ F(twist_p(f)).

Thus `ofComponents` forms an isomorphism of superfunctors without an
evenness hypothesis. `ofHom` preserves a specified homogeneous forward
map exactly; its inverse total-component formula, inverse parity and both
roundtrips are explicit. The construction works in an arbitrary target
supercategory, so the same argument applies twice without expanding
balanced coend representatives.

`ELVDistinctModuleIso.moduleMateComponentIso` uses bijectivity of the
actual total component, rather than rebuilding its source and target
module records from raw coends. `moduleMateIso` then gives the homogeneous
old-module inverse at every input module, with forward equality
`moduleMateIso_hom` and inverse parity `moduleMateIso_inv_mem`.

`moduleMate_mem` proves that the rectangular mate has crossing parity
in the input-module variable as well: the two adjunctions are even and
every other crossing component vanishes. Applying the same generic
constructor to the family `moduleMateIso` gives `moduleMateFunctorIso`.
Its forward equality is `moduleMateFunctorIso_hom`; its inverse is
supernatural in arbitrary, including odd, input-module maps, and has
parity `p(i)p(j)` by `moduleMateFunctorIso_inv_mem`.

Both producers and their concrete consumers pass strict scoped checks.
The consumers audit all 34 owned declarations. They test odd parity-change
naturality over rational superspaces and on parity-shifted old modules,
both mixed moving parities, distinct odd colours, ordinary exterior right
precomposition, empty words at zero cutoff and both inverse identities.
Full CI remains the integration gate. Transport of this particular
isomorphism through the chosen content and original weight comparisons
remains a subsequent obligation.
