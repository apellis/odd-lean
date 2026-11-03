# The selected word append comparison preserves the actual dot

Status: strict producer and occupied paired-consumer checks passed; all 10
owned declarations use only standard axioms. Full-library CI is separate.
This is the checked successor of the explicitly unverified 807a911d draft.

`ELVPowerWordAppendDot.lean` gives the full nested-tensor formula for the
literal total map of `powerWordAppendIso`. Its endpoints are the unchanged
actual raw balanced coends; normalizing those endpoint aliases avoids
unnecessary dependent reduction during Lean checking.

The selected map intertwines `actualInductionDot` with the native signed
old-Hom dot. The result is an equality of linear maps on the entire actual
induced word module. Its tensor formula allows arbitrary old arrows and
arbitrary coefficient classes, including both odd exterior colours and
inhomogeneous vectors. The parity twist of the old kernel is retained.

The paired consumer checks the literal selected-map total, the actual odd-dot
square, and an inhomogeneous regular-power coefficient vector. A bounded
half-turn coordinate proves that a two-colour exterior PBW vector survives
in that same actual three-strand next-word module. This proves occupancy of
the tested module; it does not assert that this particular vector has nonzero
dot image.

Crossing compatibility through the selected iterated word comparisons, the
remaining source-placed bubble comparisons, and assembly of the swapped
action are separate obligations. This dot square is not action faithfulness
or odd nondegeneracy.
