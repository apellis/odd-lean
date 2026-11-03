# Native probe cap normalization window

`ELVProbeCapWindow` proves the finite normalization window of the given
native inverse-unit coefficient cap. For a coefficient-evaluating probe
module and a moving colour absent from its output content, the prescribed
cap composed with its given unit/dot column is the identity on its own row
and zero on every other row in the finite window.

The proof cancels the selected scalar value chart using the checked native
cap-field comparison, the selected F/E unit/dot square, and the actual
ordinary inverse coefficient's Kronecker window. It retains the canonical
inverse-row unshift and adds no cap scalar.

For the original regular empty probe, `ProbeVacuumCap.groundRow_dot_unit`
identifies the last row's ground coordinate on every scalar input:

```
groundRow (dot^a (unitVector c)) = if a + 1 = P then c else 0,   a < P.
```

Here `dot` is the actual restricted module dot on the same native F/E
superspace as the cap, and `unitVector` uses the actual adjunction unit and
the literal empty ground coordinate. `dot_odd_polynomial` proves
`(dot^2 + 1)^m = 0` for an odd moving colour on that same superspace.
`ELVUnitDotComponents` proves the underlying module-to-component power
identities and polynomial transfer before any datum specialization.

The paired rational consumer checks positive odd-colour cutoffs 2 and 4,
extracts every scalar on the prescribed top unit/dot vectors, proves those
vectors nonzero, and checks `dot^2 v = -v` on the same occupied vector at
cutoff 2. All 11 and 38 declarations owned by the two producer modules,
including private and generated declarations, pass the standard axiom audit.
The exact producers and consumer pass strict scoped Lean checks; the full
repository CI gate remains the integration gate.

This supplies actual native probe normalization fields. A complete mixed
swapped `s/u/v/x/y` datum and its slide relation, and identification with a
separate action's left counit, are separate obligations.
