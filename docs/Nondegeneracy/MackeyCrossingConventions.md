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

## Evaluated ordered product

`leadingMoveEndpointPolynomial_eq_sign_smul_squareProduct` now proves,
for every prefix and word and either parity,

    endpoint_ν = zsign(p(i))^(count_i ν) • S_ν,
    S_ν = ordered product over b with ν_b=i of
          (z^(1+p(i)) - x_b^(1+p(i)))².

The exponent 1+p(i) means 1 for even i and 2 for odd i; the Lean
producer uses those branches explicitly. Earlier factors are on the right
in the endomorphism ring, matching chronological composition. The unsigned
product is independently defined, not defined by the endpoint expansion.
The local four-term coefficients are `[1,-1,-1,1]` for even colour and
`[-1,1,1,-1]` for odd colour. All collected crossing signs cancel:
even moving crossings have zero parity, whereas odd dot decorations occur
in pairs, squaring each incident or distant slide sign.

Old/moving separation is checked by `endpointDotMonomial_separate` and
`leadingSourceDots_oldSourceSign`. Old factors are already PBW-sorted;
`leadingSource_oldPBWCoordinate` makes every nonidentity old-permutation
coefficient zero. `prependWordCoefficients_moveHom_ordered` evaluates the
longest coordinates as an explicit finite diagonal sum.

`leadingMoveContentCoefficient_homMatrixTwist` proves the old twist fixes
these coefficients. `leadingMoveContentCoefficient_degreeSign` proves the
moving-degree normalization fixes them: odd moving dots occur in pairs.
This does not identify equal-colour count with moving-dot degree.
`appendContentMoveLift_extract_sum` gives the normalized source extraction
with no unevaluated coordinate map and with the right coefficient b unchanged.
Affine coefficients include height zero; the ordinary append source retains
its existing old-height n+1 scope.

## Remaining comparison

Equation (6) in `DeformedBoundaryDivision.md` remains a **source-convention**
identity: its (-1)^(count_i ν) is not the library sign. The corresponding
library sign (-1)^(p(i) count_i ν) is now derived from the full chain,
including scalar PBW regrouping, old twist and moving-degree normalization.
No unspecified unit from `Approx` is used.

Equation (7) is not altered: its norm, P, QP, T and right-ordered
f_i(t)L(t)t^k conventions must be compared independently. The existing
repeated-even QP factor remains -1. No full ELV boundary or corrected w_k
identification is asserted; ordinary append height zero also remains open.
