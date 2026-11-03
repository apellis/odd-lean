# Central augmented matrices in factor coordinates

For the central block of Brundan–Ellis (1.13)–(1.14),
`augPosSourceIso`, `augPosTargetIso`, `augNegSourceIso`, and
`augNegTargetIso` identify the evaluated path-family objects with
`ProbeWindow.tObj` in reservoir/probe/window order. The pure source
objects are the native postcomposition and precomposition `E F`
objects; the pure targets are the corresponding `F E` objects. Their
component isomorphisms are precisely the selected
`reservoirCapFactorIso`, `probeCapFactorIso`, `reservoirCupFactorIso`,
and `probeCupFactorIso`, in the model-to-path orientation.

`augPosSectorMatrix` and `augNegSectorMatrix` conjugate the prescribed
augmented matrices by these isomorphisms. Their `_square` theorems
are the literal coordinate squares. The `_eq_posMap` and `_eq_negMap`
theorems package every retained component into the two-sector block
shape; these statements use the entries of the conjugated matrices.
They do not yet identify each block with the separately named native
principal, bend, cap, or unit formula. That entry identification is the
next attachment step. In particular, the negative matrix is the
conjugate of `augNegMat` itself, including its prescribed minus sign;
no sign-diagonal renormalization is made.

All valid paths and all finite window indices occur. At height zero
the positive window is empty. A missing reservoir source or probe
target is represented by a zero object **after evaluation**. The native
factor families are defined only on valid-side subtypes: the chart does
not assert that a native composite vanishes at an invalid formal
content. Transferring a native factor inverse to an absent corner still
requires concrete support on the retained output blocks. The generic
`ProbeReservoir` structure does not provide that support condition.

The charts work for an arbitrary additive evaluation into a category
with a zero object, and an arbitrary full Hom object. No inverse,
coefficient-ideal membership, or uniform nilpotence bound is assumed or
proved. The paired consumer evaluates the actual positive-level ELV
factor families at arbitrary module inputs, output content blocks and
content-category objects. It includes the mixed occupied sector and
the empty sector, for both odd colours and both augmented orientations.
The generic padding consumer separately verifies nonzero rational
module entries and complementary absent-corner patterns.
