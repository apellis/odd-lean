# Bundling the inverse on untruncated old-content modules

The pointwise coend inverse in
[ContentDistinctMate](ContentDistinctMate.md) is to be assembled into a
homogeneous module inverse and an inverse supernatural in input modules.
The forward map must remain the prescribed positive rectangular
cup-crossing-cap.

For lower functors J:C→A and K:C→B and upper functors L:A→E and M:B→E,
the source on input modules is `restriction J ⋙ induction K`; the target
is `induction L ⋙ restriction M`. The upper unit and lower counit are
ordinary even adjunction maps. The crossing has parity p. Composing their
supernatural families therefore has parity p, including on odd
input-module maps.

`ELVRectangularMateIso` is proposed. It packages pointwise bijectivity of
the fixed raw rectangular map before specialization. The intended
concrete application supplies that bijectivity from
`oldContentDistinctMateLinear_bijective`, with colour hypothesis i≠j and
no additional inverse input. `HomogeneousSuperfunctorIso.ofHom` then
preserves the forward map exactly and gives inverse parity p at both the
module and input-functor levels.

The generic producer has not passed its strict check. Its remaining
elaboration obligations concern identity functors in the composed
naturality family and explicit bundled source/target parameters when
evaluating total components. The concrete old-content application and
paired consumer remain to be added. Bundled old-content and input-natural
inverses, canonical coefficient-truncated ContentModules, and
original-weight transport remain subsequent obligations.
