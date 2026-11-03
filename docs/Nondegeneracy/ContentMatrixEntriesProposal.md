# Proposed shifted entry and finite inverse attachment

The unshifted principal mate, all unit columns and all cap rows are checked
in `ContentMatrixMate.md`, `ContentMatrixUnitColumns.md` and
`ContentMatrixCaps.md`. The genuine whole finite coordinate comparisons
are checked in `ContentGridMatrixCoordinates.md`.

`ELVContentMatrixEntries.lean` proposes the remaining unit entry equation:
the chosen following F/E chart after the given grid entry equals the given
old unit entry after the selected canonical shifted coordinate chart.
It uses the same literal crossing, normalized from degree p² to p, and the
same unit/dot fields. No entry or inverse compatibility is assumed.

The proposed proof treats the principal and finite dotted slots separately.
The old fields are evaluated while their module remains abstract. The
canonical parity coordinate cancellation reduces each slot to its checked
unshifted field square. The current whole entry proof remains unchecked:
joining the concrete linear-map presentations reaches the default recursion
limit. The paired consumer is proposed only. This source is unexported and
no declaration from it is claimed.

The next step is to retain the generic column/row decoration statements
before specializing the content modules, as in the checked
`ELVProbeMatrixEntryComparison`. Explicit chart linear maps and entry
`SVec.toLinearMap` forms avoid introducing different coercion presentations.
The corresponding cap entry equation follows from the same target-coordinate
identity and the checked all-power cap square.

Summing the unit entry equations and taking the cap coordinate equations
then gives the whole finite squares. Their genuine source/target charts
transport the existing fixed-content old component inverses to bijections
of the given grid matrix components. Inverse construction applies to those
given even module maps; it must retain their prescribed forward fields.
The fixed-content backend already provides both component inverse signs
and count zero. The scope here remains untruncated old content at explicit
`i :: ν`; absent-predecessor contents and coefficient-truncated weights are
separate.
