# Actual full-ELV superadjunction

Packages the existing ordinary actual
weight induction/restriction adjunction as SKM.SuperAdjunction in its actual
PiSCat target. The even unit and counit are lifted via ofNatTrans; both
triangles reuse the proved ordinary triangles. No local inversion, family,
Morita reduction, or nilpotence assumption is supplied.

The asymmetric all-odd actual vacuum-product consumer checks the exact
unit evaluation and audits all owned declarations. This is the prerequisite
for the actual blockwise rightTranspose nilpotence construction tracked in
ELVWeightDotBounds.md; the full factor-family inverse remains open.

ordinaryEvenSuperAdjunction exposes the same constructor for the old-category
coend and Rouquier-mate comparison. It reuses an ordinary adjunction and its
proved even components; its unit and counit are exactly ofNatTrans lifts.
