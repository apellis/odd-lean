# Source coefficients through the specified tensor matrix row

The coefficient law required by SwappedVacuumCoordinates §§5–7 uses the
same matrix action and the same original-weight row observation already
constructed. It requires two squares before evaluating the source unit.

For the chosen upward path `p`, the prescribed `tensorRowTargetIso` is
the composite of the inverse factor-path object chart, the supported
vacuum-path chart, and the inverse input-weight equivalence chart.
The first two factor-path charts cancel. Naturality of
`reservoirWordFunctorIso` moves an arbitrary vacuum endomorphism through
the remaining reservoir-word chart. Equality induction on the probe
input weight commutes that endomorphism's postwhiskering with the final
input-weight transport. Applied to `tensorVacuumCoefficientAction`, this
is the checked `tensorRowTargetIso_coefficient` square. It retains the
whole SYM coefficient, including sums of even and odd terms.

The second square is for `tensorVacuumRowProjection`. Its entry is the
literal full-inclusion map followed by the factor-path object chart and
the equality identifying the terminal family with the tensor vacuum.
Naturality of the factor-path functor equality handles the former;
equality induction on the terminal object handles the latter. Thus the
checked `tensorVacuumRowProjection_coefficient` identifies the projected
matrix coefficient action with postcomposition by the same ambient
path-whiskered vacuum coefficient.

`TensorEntryPullback.map_square` transports the first square to the
original input-weight Hom in the checked `tensorRowPullback_coefficient`.
Its strict producer and concrete consumer pass, including an audit of
all 23 owned declarations. The consumer uses a nonzero two-odd tensor
row with colliding root weights and the coefficient `1 + delta`; it
proves the source row and the odd coefficient are nonzero.

The second square also passes its strict producer and concrete consumer,
with all 23 owned declarations audited. Its consumer uses the full
matrix action of `1 + delta` on the nonzero chosen matrix vacuum.
`tensorOriginalWordEntry_coefficient` now transports the composite to
the specified original Hom: applying the full matrix coefficient action
then observing the original entry is exactly path-Hom coefficient
postcomposition of that entry. The extended producer and same occupied
mixed-coefficient consumer pass, with all 24 owned declarations audited. This argument supplies coefficient
equivariance of the specified row map; identifying its evaluation on the
source unit and the subsequent quotient coordinates remains a separate
observation step. The final observation law is not a premise of either
square.
