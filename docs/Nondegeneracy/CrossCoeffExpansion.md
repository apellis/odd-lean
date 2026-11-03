# Finite component expansions of the specified crossing coefficient

`SwappedHomInversion.md` §3 (2)–(3) uses the prescribed mixed coefficient after evaluation at one reservoir component. `mixedCoefficient_even_map_expansion` and `mixedCoefficient_odd_map_expansion` prove its finite ordered expansion from the source denominator identity under an arbitrary ring homomorphism. The evaluated probe dot is a unit; the evaluated reservoir dot has the supplied exponent. Neither condition is imposed on the unevaluated ring.

The even expansion is minus the ordinary geometric sum, because the actual denominator is `y-x`. The odd expansion retains the alternating ordered powers and the square denominator; its finite window is twice the supplied annihilating exponent. Ring multiplication is functional order throughout.

`crossCoeff_even_evaluate` and `crossCoeff_odd_evaluate` specialize this calculation to the literal `c.a` of a supplied `ProbeReservoir`, using its established dot exchange and `CrossCoeff.IsInverse` equations. These are intermediate component statements: the intended factor, coefficient inverse and concrete evaluation bounds still need to be supplied by the full construction. The statements do not construct that factor or assert central invertibility.

The producer and paired algebra consumer pass strict checks; all twelve owned declarations pass the standard axiom audit. The consumer works over block matrices over Z/9, retaining two odd dots, a reservoir whose cube vanishes but whose square survives, and the negative even constant term. It evaluates a product ring at one component while the unevaluated reservoir operator has no nilpotence exponent. All exchange, denominator and component-bound hypotheses of these algebra tests are proved. This tests the component algebra; it is not an instantiation of the unfinished intended probe factor.

The next application must use the actual component-evaluation ring homomorphism and constructed coefficient, then bend the finite sums through the fixed cap/cup charts. Positive residual coefficient-ideal membership and the full augmented-matrix square remain open.
