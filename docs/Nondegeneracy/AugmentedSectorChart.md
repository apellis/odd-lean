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
`AugmentedSectorEntries` identifies each valid pure entry with
`centralFactorSigma`: the prescribed reservoir mate, reservoir-to-probe
bend, probe-to-reservoir bend, or probe mate. It similarly identifies
every cap/unit window entry with `centralFactorCap` and
`centralFactorUnit`, for its actual exponent. The `_pure_factor`,
`_cap_factor`, and `_unit_factor` theorems cancel the selected path
charts and retain only the conditional pure-slot restoration maps.
The negative principal entry is explicitly minus this same factor map.
The negative matrix is the conjugate of `augNegMat` itself, including its prescribed minus sign;
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

The paired `SwappedAugmentedSectorEntries` consumer applies the native
principal formulas at every occupied corner for both odd colours,
checks each of the four native choices separately, and retains all
natural cap/unit exponents. Its boundary window tests use a sector with
absent probe target and one with absent reservoir source; evaluation is
at arbitrary actual modules and content-category objects.

`AugmentedFactorMatrix` completes the matrix identification.
`augPosFactorMatrix` is `ProbeWindow.posMap` of the four prescribed
native principal maps and all native dotted cap rows.
`augNegFactorMatrix` is `ProbeWindow.negMap` of **minus** those same
four maps and all native dotted unit columns. Their scalar maps
`centralPaddedSigma`, `centralPaddedCap`, and `centralPaddedUnit` use
only valid native factor objects and are zero at absent corners.
`augPosSectorMatrix_eq_factorMatrix` and
`augNegSectorMatrix_eq_factorMatrix` identify every matrix entry.
The resulting `augPosFactorMatrix_square` and
`augNegFactorMatrix_square` are the literal squares from the evaluated
prescribed augmented matrices to these named native two-sector models.
No path, window index, or negative principal sign is omitted.

The paired `SwappedAugmentedFactorMatrix` consumer uses both odd colours,
the mixed occupied sector, the empty height-zero sector, and physical
ray/coray sectors whose heights are proved to be `2` and `-2`.
The latter have complementary absent probe-target/reservoir-source
corners and nonempty two-slot windows. The full Hom, module input,
output block, and content-category object remain arbitrary there.
These squares do not themselves supply native factor inverses at
absent corners, residual coefficient memberships, or an inverse of the
central augmented matrix.
