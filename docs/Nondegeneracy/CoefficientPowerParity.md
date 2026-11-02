# Parity shifts of coefficient-power modules

This supplies the parity closure required by
[CoefficientPowerModules](CoefficientPowerModules.md) for the module
category of [SwappedNondegeneracy, §2](SwappedNondegeneracy.md).
The producer and paired concrete consumer pass scoped Lean checks with
warnings as errors and both pinned compatibility settings. All four owned
declarations pass the standard axiom allowlist audit. Full CI remains the
integration gate.

An even coefficient commutes with every supernatural module map, including
an inhomogeneous one. `killsCoefficient_of_iso` applies that naturality to
the inverse component of the supplied module isomorphism. Its objectwise
linear inverse is injective, so annihilation of the coefficient transports
to the other module. No assumption that the isomorphism is even is used.

Every power of an even coefficient is even. The generator characterization
of the literal two-sided power ideal therefore proves
`coefficientPowerProperty_of_iso`. Applying it to the inverse of the
chosen odd module parity isomorphism proves
`coefficientPowerProperty_parity`.

`coefficientPowerPi` uses the existing full-subcategory Pi construction.
Its parity-shifted objects, odd comparison and inverse are the exact
old-module ones. Thus the coefficient-power-annihilated category is a
Pi-supercategory, retaining every supernatural map and both inverse
products.

The concrete connected two-odd-colour consumer uses the actual pulled-back
weighted-empty representable annihilated by an elementary even square. It
checks preservation of the entire power ideal, the parity of the literal
odd comparison, its inverse and the exact comparison selected by the new
Pi structure. This supplies parity closure; it does not identify the
weighted quotient with the power ideal or provide an evaluation kernel.
