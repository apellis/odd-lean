# The native polynomial cap on the negative unit window

This supplies the low-column part of
[SwappedVacuumNonpositiveBubbles](SwappedVacuumNonpositiveBubbles.md),
§2 (6)–(8), on the same native tensor module as the moment maps.

Let `y` be its actual reservoir dot, `u` its append unit, and `λ` the
prescribed normalized final inverse row. The actual polynomial cap is
`b' = (y² + 1)^M ≫ λ`. For every natural number `a` satisfying
`a + 2*M < cutoff i`, `tensorPolynomialCap_unit_window` proves the
whole-module-map equality

\[
u\,y^a\,b'=
\begin{cases}
1,&a+2M+1=N,\\
0,&a+2M+1\ne N.
\end{cases}
\]

The polynomial's leading coefficient is proved to be one. The given
native reservoir unit window supplies the remaining hypotheses of
`negative_cap_unit_window`. No moment or cap compatibility is assumed.
The equality applies to the entire native module, before evaluation at
an empty word or a particular vector. The formal polynomial window is
valid for either moving parity; its odd probe application takes `M=m_i`.

Together with `evaluatedMixedBend_polynomialCap_zero`, this provides the
annihilation and low-unit tests for identifying the last chosen negative
inverse row. That identification additionally requires the actual
padded bend and unit-column charts; it is not asserted here.

The consumer uses two odd colours with the asymmetric exponents `2`
and `4`, probe exponent `2`, and reservoir cutoffs `5` and `6`. It tests
the final columns and an earlier vanishing column, proves a final native
closure is nonzero using the independent exterior product `δ₀δ₁`, and
includes inhomogeneous coefficient inputs.
