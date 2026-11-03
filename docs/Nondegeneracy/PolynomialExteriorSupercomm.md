# Full coefficient supercommutativity

The signed word reversal of `SwappedVacuumCoordinates.md` §4 must reverse
composition using total parity. In a coefficient-extended Hom space this
includes exterior coefficient parity, not only affine diagram parity.

`OddMath/SKM/PolynomialExteriorSupercomm.lean` proves the needed coefficient
identity directly in the full polynomial/exterior algebra:

`a * b = (-1)^(p*q) • (b * a)`

for `a` in parity `p` and `b` in parity `q`. Its two public results are
`exteriorParity_supercomm` and `polynomialExteriorParity_supercomm`.
The proof starts with the exterior algebra's actual alternating products,
extends through the exterior-power spans and parity sums, then through
base change by the polynomial algebra. No exterior generator is specialized
or killed, and no faithfulness of bubble evaluation is assumed.

The paired consumer `scripts/NonVacuity/PolynomialExteriorSupercomm.lean`
uses two different odd colours over the rationals. It proves their product
is nonzero using the exterior basis, then applies the homogeneous theorem
to detect the minus sign. It also tests an even polynomial coefficient
against an arbitrary odd homogeneous element.

Verification: strict pinned source and paired consumer checks passed. The
consumer audits all four declarations owned by the producer,
including private and generated declarations, against `propext`,
`Classical.choice`, and `Quot.sound`.

This is the coefficient sign input for a later full half-turn composition
law; it does not assert any quotient identification or nondegeneracy theorem.
