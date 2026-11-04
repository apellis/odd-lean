# The pure probe sideways entry

Brundan–Ellis Definition 1.5, (1.11), requires an invertible distinct
sideways crossing. `ProbeReservoir.isIso_sigmaEntry_pure_probe` in
`SwappedAssembly/Sigma/DistinctPureEntries.lean` identifies the pure
probe entry with the precomposition left mate of the factor crossing.
It retains the endpoint transports between the two orders of adding
colours and the source and target content shifts.

The generic entry theorem takes `LeftMateInvertible P.T
P.T.leftAdjoints`. Its chart comparison transports the individual
crossing factors before invoking
`SKM.homContentDistinctPreMate_isIso`. The two orders have equal
weights, rather than definitionally identical weight expressions, so
the comparison retains their prescribed equality maps explicitly.

For the chosen cyclotomic probe family this factor input is constructed
by `RouquierFamily.canonicalLeftMateInvertible` from its multicolour
relations. The cap-pitchfork range and the shifted strict cup-pitchfork
range cover every weight. No factor left-mate premise is needed from
the caller of the resulting native permutation.

The paired consumer `scripts/NonVacuity/DistinctPureEntries.lean` uses
the weighted mixed-parity Boolean fixture in the actual rational
functor bicategory. It constructs occupied pure-probe paths in both
orders, proves their common endpoint, supplies the canonical factor
left-mate theorem, and applies the entry theorem on the prescribed Hom
category. Nonzero vacuum append vectors in both colours are retained.
Its owner-module audit checks all declarations against the standard
axiom allowlist.
