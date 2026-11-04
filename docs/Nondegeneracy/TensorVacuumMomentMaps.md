# Closed moments of the prescribed tensor vacuum

The all-power coefficient calculation in
[SwappedVacuumNonpositiveBubbles §2](SwappedVacuumNonpositiveBubbles.md)
uses the given reservoir unit, signed dot and normalized last inverse row.
`CyclotomicAction/ELVTensorVacuumMomentMaps` transports this calculation
from the weighted power vacuum to the literal tensor vacuum, on every
vector of the full coefficient quotient.

Let `V = H.obj N₀` be the tensor value, `e : V ≅ W₀` its prescribed even
vacuum chart, and `ell` the existing `tensorPowerVacuumCap`. The whole
module square `tensorPowerVacuumCap_moment_square` says that every actual
unit/dot column followed by `ell` and `e.hom` is `e.hom` followed by the
existing weighted column and its prescribed weighted coefficient cap.
It combines the normalized tensor-cap comparison with the actual supported
content target chart; no principal inverse is used.

The induced `tensorMomentMap` decodes the same literal closure using
`tensorVacuumDecodeLinear`, whose factors are `e` and the original empty
power-vacuum coordinate. Its inverse `tensorVacuumInputLinear` is the
literal tensor of the weighted coefficient vector with the regular probe
scalar unit. Both inverse identities are proved from the given even chart. `tensorMomentMap_eq_weightedMomentMap` identifies
all exponents with the existing weighted moment operators. In particular,
the even and odd series are respectively left multiplication by

    completeCoefficient(i,r),
    (-1)^(cutoff(i)+1) delta_i completeCoefficient(i,r).

These are operator equalities on the full coefficient quotient, including
arbitrary inhomogeneous inputs. The independent odd coefficient and the
cutoff sign retain their original order.

The remaining attachment is to the literal supported swapped inverse and
the normalized bubble definitions. The negative-height and height-zero
polynomial-cap comparisons concern the evaluated mixed bend; identifying
its prescribed inverse and carrying the normalization through the supported
whole-weight charts are separate obligations. No final bubble series or
nondegeneracy conclusion follows from this transport alone.

The polynomial cap `tensorPolynomialCap` applies `(y^2+1)^M` in the given
native restricted module dot before that same inverse row. Its literal
unit-column component is `tensorPolynomialCapMoment_moduleCap`.
The equality with `weightedPolynomialCapMoment` retains every binomial
coefficient and every input vector, and imports the established complete
moment formulas without changing operators. At `2M ≤ N` its first
normalized odd closure is `(-1)^(N+1)L_delta`; at `N=2M` it is `-L_delta`.
This is a polynomial-cap closure statement before mixed-inverse and
bubble-definition attachment.
