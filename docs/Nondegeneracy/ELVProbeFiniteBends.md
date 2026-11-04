# Finite coefficient series in the prescribed mixed bends

`Sigma/FiniteBendEvaluation` attaches the finite coefficient expansions of
`SwappedHomInversion` §3 (3)–(6) to the specified
`probeToReservoirBend` and `reservoirToProbeBend`. These are the bends in
the checked `sigmaEntry_probeToReservoir` and
`sigmaEntry_reservoirToProbe` equations. Neither bend is replaced by a
separately defined regular-probe diagonal.

Fix an output evaluation functor `L`. Write `γD` for
`probeToReservoirCoefficientIso` and `γC` for
`reservoirToProbeCoefficientChart`, with the inputs prescribed in those
definitions. The coefficient evaluations are the ring maps

    ΦD = L ∘ FR ∘ Ad(γD),
    ΦC = L ∘ FP ∘ Ad(γC),

where `Ad(γ)(a) = γ.inv ; a ; γ.hom`. Let `BD` insert an evaluated
coefficient between the chosen reservoir unit and probe counit. Let
`BC` insert it between the chosen probe unit and reservoir counit. The
exact evaluated bend equations are

    L(Dx) = BD(ΦD(c.a)),
    L(Cx) = -BC(ΦC(c.a)).

In particular, the second equation retains the negative PR conjugation.
The insertion maps are additive and retain the order of every
coefficient monomial.

`ELVProbeBendEvaluation` supplies literal total evaluation on the full
Hom category. Its parity-component ring map identifies the extra
output parity shift with the prescribed componentwise conjugation and
twist. Its reservoir-restriction comparison reads exactly
`blockSucc δ`, where `δ` is the requested output reservoir block.
Probe precomposition instead reads the transformed probe input and
the same reservoir block. Thus the reservoir-dot bounds can be taken
at these components, rather than on a whole weight fibre.

`ELVProbeFiniteBends` uses these comparisons with
`elvProbeCrossCoeff`, the coefficient chosen from the constructed
denominator units. Its four expansion theorems have no inverse identity,
probe-unit premise, or nilpotence-bound premise. If `X = Φ(rpPreDot)`
and `Y = Φ(rpPostDot)`, each constructs `n` with `Y^n = 0`. At an even
colour the evaluated coefficient is

    -Σ(r < n) X⁻¹^(r+1) Y^r.

At an odd colour it is

    Σ(r < 2n) (-1)^r X⁻¹^(r+1) Y^r.

Applying `BD` or `-BC` gives the stated finite bend series. The whole
probe-dot unit is transported through the exact charts and lowering
functor before taking the displayed inverse. The statements retain
arbitrary input Hom objects and supported probe and reservoir inputs.

`Sigma/BendDotCoordinates` now checks the four raw chart comparisons
before lowering and evaluation. The XP-to-YR chart carries the inner
probe dot to `ER.map (homReservoirDot U)` and the outer reservoir dot
to `homContentPostDot (EP.obj U)`. The XR-to-YP chart carries them to
`q • homReservoirDot (ER.obj U)` and
`q • EP.map (homContentPostDot U)`, respectively, where
`q = koszulSign (D.parity i) (D.parity i)`. Both signs therefore come
from the prescribed mixed interchange. These comparisons retain the
full transported input Hom object and require no new chart hypotheses.
Their paired consumer uses the actual ELV factor at the specified
lowered objects, including both parity corners at nonempty sectors.

The remaining monomial comparison is separate: identify each insertion
term with the separated chosen dotted reservoir cap/cup, probe unit/cap,
and inverse probe-dot powers in the literal `hCx` and `hDx` hypotheses
of `CentralInverse/ResidualComparison`. The insertion series alone does
not discharge those hypotheses, the off-window contractions, or the
positive coefficient-ideal memberships of the closed errors. In
particular, a formula for an independently defined regular-probe bend
cannot replace this comparison on arbitrary supported Hom objects.

All three producers and their paired `ELVProbeFiniteBends` consumer pass
strict scoped checks with the pinned toolchain, warnings as errors and
both compatibility settings. The consumer audits every owned declaration
in all three modules against the standard axiom allowlist and supplies
nonzero probe vacuum vectors in both moving parities.
