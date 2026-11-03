# The rank-one probe weight principal entry

Brundan–Ellis (1.13)–(1.14) uses the selected negative equal crossing
between the chosen upper unit and lower counit.
`probeOldBlockEqualCross_stored_eq` identifies the whole block crossing
with `probeAppendToEqualCross` at the literal stored representatives.
`probeOldWeightRouquierMate_comparison` pastes the crossing square with
the selected unit and counit squares. It identifies every parity
component of the occupied weight principal map with
`probeAppendToMate` through the specified source and target equalities.
No inverse or comparison premise is supplied.

`probeOldWeightRouquierMate_eq` and
`probeOldWeightRouquierMate_mem` keep the chosen rank-one mate and its
required colour parity.

The producer and paired concrete consumer pass strict scoped checks.
The consumer audits all 55 owned declarations against the repository
axiom allowlist and applies both the crossing identity and principal
comparison to regular mixed-parity weight arrays and parity shifts.
