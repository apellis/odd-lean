# Prescribed cap on the precomposition Hom carrier

For `SwappedActionAssembly.md`, §5 (A14) and §6, the cap and dot are
transported by the lower Hom-sector construction, without an assumed
complete Rouquier family. `modulePiCategory` retains the existing
empty-content module category and its given vector parity.

`capCell` is the prescribed last inverse coefficient row, using its
input-supernatural family of degree `(P-1)p`. `dotCell` is the restricted
induction dot of degree `p`. Their regular-probe components are exactly
`ProbeVacuumCap.cap` and `moduleDot`, respectively.

`preCap` and `preDot` are the existing `SKM.homPreTransform` applied to
these 2-cells. Thus their naturality on arbitrary homogeneous reservoir
maps includes super-interchange. `preCap_total` and `preDot_total` identify
their evaluations with the images of those specified module maps.
`preCap_dot_unit` retains the normalized extraction window, and
`preDot_odd_polynomial` retains `(D²+1)^m=0` on that same evaluated dot.
The consumer uses the actual native parity functor as reservoir, so odd
maps are transported by its given action rather than unsigned identity.

The canonical source parity comparison, a normalized left unit with both
triangle identities, and identification with the transpose dot of (A14)
remain distinct obligations. No left adjunction or mixed slide is asserted.
