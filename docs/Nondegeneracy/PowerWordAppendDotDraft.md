# Proposed selected power-word append/dot attachment — UNVERIFIED SNAPSHOT

This is an hourly history-preservation snapshot, not checked library source.
`ELVPowerWordAppendDot.lean` is NOT exported. Its full producer currently FAILS
strict Lean checking, and no paired consumer has been completed. Do not use
this snapshot as a checked comparison theorem.

The draft targets the selected `powerWordAppendIso` total map on arbitrary
nested coefficient vectors, then an equality of linear maps intertwining the
actual chosen induction dot with the native signed old-Hom dot.

The generic induction-composition/functor-equality tensor helper checks; the
separate generic native transformation tensor probe also checks. The actual
specialization still needs redesign of raw endpoint normalization: matching
the selected total map with its raw composition times out under the fixed
200000-heartbeat budget. The dot specialization also has an explicit-argument
mismatch to repair. The all-vector extension is not yet checked. No proof
budget was raised and no new axiom, `sorry`, or assumed comparison was added.

The checked preceding Yoneda and native-map publications are ec131630 and
57a836e6. Their exact source, consumers and notes are separate from this draft.
