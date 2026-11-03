# Weighted matrix inverse comparison

This proposed source targets DeformedMatrixComparison (2), (4), transporting
the prescribed arbitrary-module old unit/cap matrix inverses to the given
weighted finite matrices, with their canonical parity coordinates.

`ELVWeightedMatrixInverse` constructs the Option–Fin coordinate equivalences
from the selected append source/target charts and the actual module parity
isomorphisms. Their products transport the given `moduleUnitMatrixIso` and
`moduleCapMatrixIso`, using the actual content height hypotheses. There is
no additional inverse or flatness hypothesis. The draft also attaches the
given ordinary unit/dot and dot/counit rows and the given first mate entry
to those charts.

The producer and paired consumer are unverified as a whole. The finite
coordinate equivalences and transported isomorphism constructions have
passed preliminary checks, and both all-power ordinary unit/cap row squares have
passed inside the draft. The current failure is final equality-chain
normalization for the mate value square. Forward identification
of the transported isomorphisms with `weightedUnitMatrixComponent` and
`weightedCapMatrixComponent` remains unproved. Thus this proposal does not
yet establish inverses for the prescribed weighted matrices.
