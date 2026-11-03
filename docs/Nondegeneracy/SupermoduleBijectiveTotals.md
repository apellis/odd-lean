# Homogeneous module inverses from bijective totals

Brundan–Ellis (1.12)–(1.14) require the specified module maps to be
invertible, including their supernatural structure. The constructor
`HomogeneousSuperfunctorIso.ofBijectiveTotals` takes a homogeneous
supermodule morphism and bijectivity of its total component at each object.
It constructs the inverse using the corresponding pointwise linear
equivalences and the homogeneous inverse naturality theorem.

The forward map is definitionally the specified map up to the public
`ofBijectiveTotals_hom` equation. Both inverse identities use that map,
and `ofBijectiveTotals_inv_mem` retains its parity. In particular the
constructor applies to odd maps, without replacing their twisted
naturality by ordinary naturality.

The paired consumer applies the constructor to the identity and to the
odd canonical parity isomorphism of the connected two-colour truncated
representable module. Every declaration of the producer is audited
against `propext`, `Classical.choice`, and `Quot.sound`.

This supplies the pointwise-to-module step for the prescribed finite
matrix inverses; it does not assert any additional matrix bijectivity.
