# Source and library crossings in the moving chain

The convention in `DeformedBoundaryDivision.md` §2–§4 is the source
crossing τ. In the library's signed nilHecke family it is

    τ = -ε T,    ε = (-1)^p.

Thus τ = -T at even colour and τ = T at odd colour. Neither `moveHom`
nor the prescribed extraction map is changed by this comparison.

Put E = v-u and D = v²-u². The local identities proved in
`AppendContentMoveCoordinates.lean` are

| Colour | Source expression after substitution | Library expansion |
|---|---|---|
| even | E(1-E(-T)) | E + E²T |
| odd | D(E-DT) | DE - D²T |

The declarations `movingEven_sourceCrossing`, `movingOdd_sourceCrossing`,
`movingEven_crossingCoefficient` and `movingOdd_crossingCoefficient`
prove these identities in an arbitrary ring. Consequently the coefficient
of the library crossing is positive at even colour and negative at odd
colour. These local identities are not descended boundary identities or
counterexamples to one.

## General source and extraction

For arbitrary old height n+1, content β and right coefficient b,
`appendContentMoveLift` constructs the tensor of the prescribed content
moving chain with b, in the actual append-fixed source. The right prepend
corner and left append corner conditions are proved, not assumed.

Write cₘ for the affine prepend coefficient of `contentMove` at
`(longPrependShuffle (n+1), m)`, and ε for `appendContentParity`.
`appendContentMoveLift_extract` gives exactly

    B₁(G ⊗ b)ₘ = (-1)^(m p(i) sumParity(β)) · (twist_ε(cₘ) · b).

The displayed order is part of the statement: the twisted old coefficient
acts on b before the integer sign. This includes the degree normalization
in `movingSignNormalize`; it does not identify cₘ with a proposed norm
coefficient.

`canWord_longPrependShuffle` identifies the canonical word literally with
the descending run, whose chronological diagram word is the ascending
sequence of crossings. `prependBasis_long_repr_eq_zero_of_low` proves
that every term with fewer than n+1 crossings has zero long scalar PBW
coordinate, even when that coordinate carries an old permutation.

## Remaining comparison

Equation (6) in `DeformedBoundaryDivision.md` remains a **source-convention**
identity. Its factor (-1)^m must not be copied into the library crossing
convention. Deriving the library expression requires the explicit signed
leading-polynomial expansion of the entire chain, conversion from scalar
PBW coefficients to `prependCoefficients`, and the displayed twist and
degree normalization. `LeadingMovePolynomial.lean` now proves the actual
finite chronological endpoint expansion of `leadingMoveHom` and `moveHom`
modulo lower crossing length. `LeadingMoveCoefficients.lean` proves its
scalar-to-old-matrix coefficient comparison and the corresponding extraction,
retaining the displayed twist and degree sign. Sorting old and moving dots,
evaluating the residual `prependWordCoefficients`, and identifying the ordered
product S remain open. None of these steps is replaced by a supplied
injectivity or extraction hypothesis; `Approx` alone retains an unspecified
leading unit and is insufficient.

The local library factors suggest (-1)^(p(i)m), but the full normalized
coefficient identity is not yet formalized. Equation (7) is not altered:
its P, QP and T conventions must be compared independently. The existing
repeated-even QP factor remains -1.
