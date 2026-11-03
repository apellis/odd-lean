# Canonical shifted target comparison through restriction

The prescribed shifted unit/cap entries in DeformedMatrixComparison (5), (6)
use the existing `homParityShiftDatum` objects and coordinates in the two
supermodule categories. A comparison of unshifted vectors alone does not
attach those chosen parity targets or their module actions.

For a superfunctor `Q : C ⥤ D`, an ordinary module `M`, an old module `N`,
and an isomorphism `e : Res_Q M ≅ N`, `parityRestrictionIso` is constructed
from the inverse of the existing `homParityShiftCommute` for `Res_Q`,
followed by the old shift functor applied to `e`. Its source is
`Res_Q(Π^q M)` and its target is the actual `Π^q N`.

For even `e`, `parityRestrictionIso_eq_chain` identifies this canonical map
with `Res_Q(ζ_M) ≫ e ≫ ζ_N⁻¹`. Its two degree-`q` coordinates cancel, so
both bridge directions are even. The hom/inverse-coordinate theorems give
the exact target-coordinate square needed by the already checked scalar
cap-row comparison.

`parityRestrictionNatIso` performs the same construction for an entire
input-natural family `e : F ⋙ Res_Q ≅ G`, by whiskering the canonical
shift-commutation isomorphism and then the family. It is an ordinary natural
isomorphism on every input map, including odd and inhomogeneous maps of
supermodules. Its component equals the pointwise bridge. Even family
components give even bridge components.

The producer and consumer pass strict pinned checks, including the owned
axiom audit. The consumer uses the
actual scalar quotient functor, canonical connected mixed/vacuum probe
module value isomorphisms, every parity shift, and a full ordinary-module
family whose odd/inhomogeneous input map includes the actual induction dot.
The scalar shifted cap-entry attachment and
finite matrix assembly remain separate obligations. No naked output parity
map is tensored as an ordinary bimodule map.
