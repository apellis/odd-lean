# Right products by independent S at even moving colour

This is the parity-zero monic-S algebra needed in
[DeformedBoundaryDivision](DeformedBoundaryDivision.md), section 5.
The operator remains the existing `independentSRightProduct`.

At even moving colour i, every coefficient twist n·parity(i) vanishes,
at every degree n. Its full-coefficient action is consequently literal
chronological convolution by independent S. No support-even property of S
is used, and no restriction is imposed on exterior coefficients or other
colours.

Monicity implies that an input supported through M has its coefficient at M
read back at M+degree(S) in the product. Taking a largest supported input
coefficient therefore detects any proposed upper bound. It also proves
uniqueness of a quotient with remainder supported strictly below degree(S).
The arguments include zero old corners and degree(S)=0.

The proposed producer is `ELVEvenSRightProduct`. It preserves the odd API
and reuses the independently defined S and its checked generic monicity.
Concrete mixed-data top/convolution/uniqueness consumers and an all-owned
axiom audit accompany it; they require checking. This is the product algebra,
not an actual boundary-leading theorem or a categorical inverse.
