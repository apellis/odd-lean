# Weighted dotted matrix rows

This is a proposed, unverified source snapshot and is not part of the
checked library. The generic dot power needs an explicit module-endomorphism
interface. The selected weighted unit/cap comparison and component inverse
transport remain to be attached.

The intended result is DeformedMatrixComparison (2), (4) on truncated modules:
the ordinary unit followed by each dot power, and each dot power followed by
the ordinary counit, agree with the corresponding given old rows through
`weightedMateSourceLinearEquiv` and `weightedMateTargetLinearEquiv`.
The finite source and target parity coordinates then transport the prescribed
`moduleUnitMatrixIso` and `moduleCapMatrixIso`; no invertibility hypothesis
on the comparison charts is to be introduced.

The draft first evaluates the actual unit/dot and dot/counit module maps on
literal coends with the append functor and input module abstract. The paired
consumer proposes both moving parities and arbitrary powers on the mixed
and vacuum representables. No scoped verification of these new rows or
component matrix inverses is claimed here.
