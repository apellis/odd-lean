# Canonical separated ELV mixed bends

`ELVProbeSeparatedBends` specializes the separated series of
`SwappedHomInversion` §3 (4)–(6) to the chosen coefficient
`elvProbeCrossCoeff`. The factor probe-dot inverse comes from the
constructed whole probe unit. The formulas use the actual
`probeToReservoirBend` and `reservoirToProbeBend` on arbitrary supported
Hom objects.

Fix `i`, a sector `t`, a Hom object `Z`, a supported probe input `M`,
and an output reservoir block `δ`. Let `L` be the literal output
functor `elvProbeBendOutputEvaluation`, and let

    q = koszulSign (D.parity i) (D.parity i).

The predicates `ELVProbeDxSeparatedAt` and `ELVProbeCxSeparatedAt`
contain the exact finite equations used as `hDx` and `hCx` in
`CentralInverse/ResidualComparison`:

    L(Dx) = -Σ(r < N) q^(r+1) • (x^(-r-1).hom ; v ; uR(r)),
    L(Cx) =  Σ(r < N) q^(r+2) • (vR(r) ; u ; y^(-r-1).hom).

Here `v` and `u` are the evaluated counit and unit of the specified
normalized probe Hom adjunction. The reservoir entries `uR(r)` and
`vR(r)` are the evaluated chosen dotted postcomposition cup and cap.
The automorphisms `x = elvProbeDxAut` and `y = elvProbeCxAut` retain
the constructed probe inverse, the prescribed probe right adjoint,
and its parity shift. Their integral powers have exactly the exponent
`-(r : ℤ) - 1`; they are not unrelated inverses chosen from a matrix
identity.

The individual separated-window theorems construct a finite count.
`elvProbe_central_separated_windows_above` constructs one count `N`
for both equations and proves `minimum ≤ N` for any requested finite
lower cutoff. It first takes a maximum of the two output nilpotence
bounds and the requested cutoff. At an even colour the series uses
that bound; at an odd colour it uses twice that bound. No common
nilpotence exponent across a reservoir weight fibre is required.

These statements evaluate at a fixed `M` and `δ`. They do not by
themselves identify the whole probe-to-output-content functor morphism
used by the coefficient ideal. The separate uniform-in-`M` comparison
must keep `δ` fixed and use the generic arbitrary-additive-output
series. Neither the pointwise series nor their common count supplies
the off-window contractions or the closed-error memberships in `J₁`.

The producer and `scripts/NonVacuity/ELVProbeSeparatedBends.lean` pass
strict scoped checks. The consumer applies both individual formulas,
the common count at both parity corners, and the common count above an
arbitrary finite cutoff to the nonzero weighted-append fixture. It audits
all 25 owned canonical declarations and the 93 and 41 owned declarations
of the two generic series modules against the standard axiom allowlist.
