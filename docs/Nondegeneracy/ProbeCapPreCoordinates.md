# Canonical source coordinates of the prescribed probe cap

The source block in `SwappedActionAssembly.md`, §5 (A14), uses precomposition
by induction and restriction, with the canonical shift of degree
`σ=(P-1)p`. `ELVProbeCapPreCoordinates` uses the existing `homPiLeft`
structure on Hom supercategories. Its `preSource` is exactly precomposition
by induction applied to the given homogeneous shift-removal isomorphism,
followed by the inverse even associator, in the order of
`homContentPreInverseSource`.

`shiftedPreCap` evaluates the prescribed cap 2-cell after that comparison.
Its forward field is identified by `shiftedPreCap_eq`, and
`shiftedPreCap_mem` proves it even by combining two degree-σ maps.
`coordinatePreDotPower` conjugates the previously identified same module
dot into these coordinates, preserves powers and `(D²+1)^m=0`, and its
composition with the shifted given ordinary unit and cap retains the
normalization window.

This coordinate dot is deliberately distinguished from the raw induction
dot acting on the shifted Hom block: moving the latter past the source
comparison contributes the Koszul factor `(-1)^(npσ)` to its nth power.
That raw-dot comparison, its power signs, and the transpose dot of (A14)
are separate obligations. The transpose identification also requires a
normalized native left unit and its signed triangle identities. No
complete Rouquier family, left adjunction, or mixed slide is assumed here.

The consumer uses the regular rational probe at odd cutoffs 2 and 4 and
uses the actual parity functor as reservoir. It checks cap evenness, every
column in the window, all dot powers, and the signed polynomial.
