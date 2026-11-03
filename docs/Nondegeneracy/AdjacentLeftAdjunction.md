# Existing left-adjunction inputs and normalization

Brundan's Theorem 4.3 already has its generic signed proof in
`RouquierPitchfork` and `RouquierFTriangle`. In particular
`RouquierFamily.leftZigzags` and `leftAdjoints` in the latter module remove
the open zigzag premise described in the earlier `RouquierLeftCupCap`
module docstring. That earlier docstring records the scope of that module,
not the current endpoint of the later proof.

For one edge, the proof uses three given even right adjunctions and two
adjacent `SuperRouquierLoc` records L and U at heights h and h+2. Each
local record contains the homogeneous dots and equal-colour crossing,
both signed slides, and the positive and negative augmented inverses.
The additional equations are square zero for both equal-colour crossings
and the braid on the three raising edges. No distinct-colour quadratic,
distinct-colour braid, mixed inverse, or pre-existing left zigzag is used.

`SuperRouquierLoc.negativeLeftAdjunction` packages exactly these inputs
at h<0. Its unit is U.cupL and its counit is
`koszulSign σ σ • L.capL`, where σ=p(h+1). This equals c(h)⁻¹ times the
raw inverse row, with c(h)=(-1)^σ at negative height. When σ=1 the native
normalized counit is the negative of that row. The constructor changes
no prescribed cup/cap gauge.

`HomSectorTransport.md` (4), kernel-checked as
`homContentPreAdjunction_leftAdjoints_counit_app`, contributes a second
`koszulSign σ σ` on the output-shifted pre-Hom counit. At negative height
the two factors cancel. Thus the raw inverse-row normalization on the
pre-Hom carrier does not identify the native normalized counit with that
row. No `ShiftedSuperAdjunction.rescale` API is used or required.

The generic consumer supplies all square and braid equations from its
rank-one Rouquier input and checks the odd negative-height minus. That
input family remains data; no native family is constructed by this batch.
The separate probe row comparison supplies its nonzero cap and the
uniqueness of that row from the actual unit-column inverse.
