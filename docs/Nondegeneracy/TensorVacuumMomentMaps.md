# Closed moments of the prescribed tensor vacuum

The all-power coefficient calculation in
[SwappedVacuumNonpositiveBubbles §2](SwappedVacuumNonpositiveBubbles.md)
uses the given reservoir unit, signed dot and normalized last inverse row.
`CyclotomicAction/ELVTensorVacuumMomentMaps` transports this calculation
from the weighted power vacuum to the literal tensor vacuum, on every
native vector and every vector of the full coefficient quotient.

Let `V = H.obj N₀` be the tensor value, `e : V ≅ W₀` its prescribed even
vacuum chart, and `ell` the existing `tensorPowerVacuumCap`. The whole
module square `tensorPowerVacuumCap_moment_square` says that every actual
unit/dot column followed by `ell` and `e.hom` is `e.hom` followed by the
existing weighted column and its prescribed weighted coefficient cap.
It combines the normalized tensor-cap comparison with the actual supported
content target chart; no principal inverse is used.

`tensorVacuumDecodeLinear` decodes through `e` and the original empty
power-vacuum coordinate. Its inverse `tensorVacuumInputLinear` is the
literal tensor of the weighted coefficient vector with the regular probe
scalar unit. Both inverse identities retain every native tensor vector.

`tensorPowerVacuumCap_moment_weighted` identifies the decoded closure
with the existing `weightedMomentMap` applied to the decoded input.
`tensorPowerVacuumCap_moment_apply` gives left multiplication by the
original signed moment. Its even and odd specializations retain

    completeCoefficient(i,r),
    (-1)^(cutoff(i)+1) delta_i completeCoefficient(i,r).

These identities hold on every native vector, including arbitrary
inhomogeneous coefficient inputs. The independent odd coefficient and
the cutoff sign retain their original multiplication order.

The polynomial cap `tensorPolynomialCap` applies `(y^2+1)^M` in the given
native restricted module dot before that same inverse row.
The binomial expansion is evaluated after the given native maps, with
every coefficient retained. `tensorPolynomialCap_moment_apply`
identifies every decoded native closure with the existing
`weightedPolynomialCapMoment` on the decoded input. At `2M ≤ N` its first
normalized odd closure is `(-1)^(N+1)L_delta`; at `N=2M` it is `-L_delta`.

The paired `scripts/NonVacuity/ELVTensorVacuumMomentMaps.lean`
consumer uses two independent odd colours with cutoffs four and five and
probe multiplicity two, giving height zero and height minus one.
Their exterior product survives in the coefficient quotient and detects
the multiplication order of a nonzero native polynomial-cap output.
The examples include an inhomogeneous input, the higher coefficient
`e(i,0)+2`, arbitrary native vectors, and an even moving colour in a
mixed datum. The consumer also audits the module's declarations against
the standard axiom allowlist.

The remaining attachment is to the literal supported swapped inverse and
the normalized bubble definitions. The negative-height and height-zero
polynomial-cap comparisons concern the evaluated mixed bend; identifying
its prescribed inverse and carrying the normalization through the supported
whole-weight charts are separate obligations. No final bubble series or
nondegeneracy conclusion follows from this transport alone.
