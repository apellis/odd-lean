# Actual probe slide and windows on padded supported sectors

This supplies the pure-probe slide and nonnegative window inputs of
`CentralInverse/ResidualComparison`, from SwappedHomInversion §2 (1)
and §3 (6). It uses the prescribed OLD probe and ELV reservoir. The
output functor remains arbitrary and additive, so a whole-output-content
projection and a further component evaluation are both specializations.

Write `XP` and `YP` for the literal padded probe source and target
corners of `centralPaddedSigma`, and `O = E.obj Z`. Set

    sP = centralPaddedSigma c i t Z E true true,
    v = centralPaddedCap i t Z E true 0,
    u = centralPaddedUnit i t Z E true 0,
    q = koszulSign (D.parity i) (D.parity i).

`ProbeReservoir.centralPaddedProbeX` is the actual raw probe dot on
`EP(FP Z)`, evaluated and conjugated by `centralSourceCornerIso`.
Here `EP` and `FP` use `P.muP_preE i t`. At an occupied target,
`centralPaddedProbeY` is the actual raw dot on `Z`, mapped through the
normalized right adjoint `FP`, evaluated, and conjugated by
`centralTargetCornerIso`; this pair uses `P.muP_preF i hb`.
These are exactly the native automorphisms of the separated `hDx` and
`hCx` series, with the actual model-to-native corner charts attached.
No dot transpose or regular-input replacement is introduced.

The generic construction takes a proof that the prescribed probe dots
are invertible. The supported OLD/ELV interface discharges that premise
with `elvProbeReservoir_dot_isUnit`. The source and target automorphisms
are named `SupportedSectors.probeWindowX` and `probeWindowY`.

`SupportedSectors.probe_slide` proves the literal equation

    sP ; y.hom - q • (x.hom ; sP) = v ; u.

It is obtained by taking the even component of
`homContentPreMate_slide`, whose principal is the prescribed normalized
precomposition mate, then applying the output functor and the two
corner charts. The counit includes its existing normalization scalar;
the right adjoint retains its existing parity shift. The slide does not
assume a principal inverse.

For every natural exponent `n`, `probe_cap_power` and `probe_unit_power`
prove

    centralPaddedCap ... true n = (x ^ (n : ℤ)).hom ; v,
    centralPaddedUnit ... true n = u ; (y ^ (n : ℤ)).hom.

Their native inputs are the given `homReservoirCap` and
`homReservoirCup`, rather than windows defined by these desired
equations. The cap and unit power transfer needs only functoriality;
additivity is used for the evaluated slide. There is no local-height
hypothesis, so these statements include the common height-zero boundary
and every exponent needed by a fused finite window.

The probe source is always an occupied formal corner. At an absent
probe target, the target is the literal padded zero object. The target
automorphism is its unique automorphism, and all slide and unit-column
maps into that target agree by the zero-object property. This convention
also agrees with the actual native dot:
`probeWindowY_of_absent_native` compares it to the prescribed dot
transported through `probeWindowTargetZeroIso`. The latter uses
`probeTarget_absent_isZero` on the supported whole Hom object, with the
normalized precomposition roundtrip and any supplied native predecessor
edge. It does not assert vanishing of an entire original-weight fibre.

The separate consumer is
`scripts/NonVacuity/SupportedProbeSlideWindow.lean`. It retains a proved
nonzero exact-support tensor Hom for two odd colours over `ℚ`, with
Cartan matrix `[[2,-2],[-2,2]]`, cutoff `20` and OLD probe multiplicity
`10`. It applies every nonnegative window exponent, the actual slide,
both automorphism inverse identities and the native absent-target
comparison. Additional applications retain arbitrary Hom and module
inputs at an occupied target and at a proved zero local height.

These equations discharge the pure-probe dot, slide and nonnegative
window premises. They do not supply the mixed-bend finite expansions,
the contracted reservoir coefficient memberships, residual inversion,
or the final central augmented inverse.
