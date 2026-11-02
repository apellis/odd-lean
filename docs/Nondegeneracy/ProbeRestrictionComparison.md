# Scalar descent of append restriction

**Scoped-checked; full CI pending.** The producer and its paired connected,
mixed-parity consumer pass the pinned strict checks. The consumer audits all
21 owned declarations against the standard axiom allowlist.

This advances the ordinary-probe transport obligation in STATUS critical-chain
item 3 and the specified adjunction in DeformedActionAssembly §5.
`probeOldRestriction_evaluatesCoefficients` proves that restriction along the
actual old content append preserves the entire scalar coefficient evaluation
condition. The proof uses the literal coefficient-append identity, including
the odd coefficient kernel.

`probeOrdinaryRestrictionModule_eq` identifies the descended old restriction
with restriction along the chosen ordinary append functor. It is an equality
of supermodules, with the same vector spaces and arbitrary-arrow actions.
Fullness of the scalar quotient lifts each ordinary arrow to an old arrow;
the append/specialization square and the established scalar module action
identify the two maps. No faithfulness of scalar specialization is assumed.

`probeRestrictionEqToHom_app` gives identity in parity zero and zero in parity
one for the equality comparison. Thus no vector rescaling or parity twist is
introduced by this restriction comparison.

The consumer uses actual scalar-evaluated regular probe modules on connected
two-colour data, with one even and one odd colour. It checks both moving
parities on mixed content and restriction from one strand to empty content.

Preservation of the chosen ordinary counit still requires composing the
append and restriction comparisons and computing the resulting coend map.
Normalized caps, crossings and inverse matrices remain separate obligations.
