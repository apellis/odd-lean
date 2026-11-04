# Source coefficients on supported tensor words

`SupportedSectors.tensorVacuumCoefficientAction` acts by the original
`SYM D k` ring on the literal `SupportedSectors.tensorVacuum`. The action
is the whole-input map from `VacuumTensorCoefficientMaps`, transported
through the proved formal probe-weight equality and retained by the
supported full inclusion.

`tensorPathCoefficientAction` maps that same endomorphism through the
specified supported `pathFunctor`. `tensorSourceCoefficientAction` is its
specialization to the chosen fixed-source path and therefore acts on the
whole `tensorSourceObject`, with no evaluation or cyclic-unit selection.
`tensorWordHomCoefficientAction` gives an algebra map to linear
endomorphisms of the entire Hom from an arbitrary supported source object
to that path value. Its application is literal postcomposition. These
algebra maps preserve source multiplication order, including odd and
inhomogeneous coefficients.

`tensorTargetFamilyCoefficientAction` extends the same action to every
formal sector of the chosen target family; off its occupied vacuum
sector, the target is a proved zero object and its endomorphism algebra
has a unique action. `tensorFamilyPathCoefficientAction` and
`tensorFamilyWordHomCoefficientAction` therefore retain the entire
chosen families on all formal source and target sectors. The latter is
an algebra map on precisely the Hom from the selected fixed-word source
family to the prescribed path value of the selected target family.

`tensorVacuumCoefficientAction_ne_zero` says that a nonzero whole-input
source coefficient remains nonzero after the input-weight presentation
and supported full inclusion. Its concrete consumer uses two independent
odd colours: one odd source coefficient acts on a tensor carrying the
other, and bounded coefficient injectivity proves that their product
survives. Thus the corresponding coefficient endomorphism of the literal
supported tensor vacuum is nonzero. The same consumer checks the sign
under reversing these odd coefficients and the coefficient algebra law
on the whole supported path-Hom.

These declarations supply the full supported coefficient action. They
do not identify it under the global word chart or prove coefficient
compatibility of the matrix quotient observation. That comparison still
requires the global coefficient word square described in
`TensorVacuumCoefficientMaps.md`.
