# The polynomial candidate for the extreme negative-height cap

This is the algebraic inverse-row test in
[SwappedVacuumNonpositiveBubbles, §3](SwappedVacuumNonpositiveBubbles.md).
It supports research issue #345 and the bounded recovery construction.
The principal-inverse case is separate in [InverseCapMoments](InverseCapMoments.md).

Let the reservoir degree be N and the probe polynomial degree P<N.
In the literal homogeneous coordinates assume

    y s-q s x=u v,
    ell y^a u=[a=N-1] (0≤a<N),
    g(x)=0,   g(T)=sum_(n=0)^P c_n T^n,
    c_n q^n=c_n.

The signed coefficient-window recurrence already proved for the principal
case gives `ell y^n s=q^n ell s x^n` for every n≤P. Consequently

    ell g(y)s=ell s g(x)=0.

If g is monic, coefficient extraction on the unit columns also gives

    ell g(y)y^a u=[a=N-P-1],   0≤a<N-P.

Every exponent used here is below N, so these values follow from the
normalizing window alone. No uncomputed large-dot moment is used.
The displayed maps therefore have exactly the inverse-row tests for the
extreme cap of `[s,u,yu,...,y^(N-P-1)u]`. Identifying this row with the
prescribed augmented inverse uses uniqueness of that inverse, rather
than choosing a cap to force its moments.

`SwappedVacuum/NegativeCapMoments.lean` proves
`coefficient_polynomial_moment`, `negative_cap_annihilates_mate` and
`negative_cap_unit_window`. The paired consumer
`scripts/NonVacuity/SwappedNegativeCapMoments.lean` verifies all inputs at
N=2,P=1 on occupied rational modules: the reservoir dot is nonzero
nilpotent, the mate and unit form an invertible two-column matrix, and the
candidate is its literal extreme inverse row. All owned declarations are
audited against the standard axiom allowlist.

The producer and consumer pass scoped checks with warnings as errors.
Full CI is the integration gate. The result does not construct the actual
swapped action, its monic-remainder functional, or its normalized
adjunction. The remaining attachment must supply these literal inputs
from the actual coefficient algebra and match the homogeneous maps to
the chosen augmented inverse. Computing the full high-dot moments and
the resulting bubble series remains separate.

The producer, owned axiom audit and all concrete consumers passed full CI
at source head `39301885c8edff5e07c020246ff86ad5ebd0da5a`, integrated in [#956](https://github.com/apellis/odd-lean/pull/956).
