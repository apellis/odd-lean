# Actual finite component matrix isomorphisms

Brundan--Ellis (1.13)--(1.14) and DeformedMatrixComparison section 4
require the actual finite entry matrices, with their prescribed parity
shifts, rather than only an invertible coordinate formula.
ELVFiniteMatrixComponents assembles those literal maps as superspace
morphisms.

unitMatrixComponent is the finite sum of unitMatrixEntry totals.
capMatrixComponent is the vector of capMatrixEntry totals.
Their source and target superspaces have pointwise grading on the
actual shifted module families. Both assembled maps are even for every
old supermodule and every moving colour.

The named first-source and first-target parity isomorphisms expose
literal module endpoints. They identify the none entries with the
fixed ordered mate, without unfolding a parity-dependent coend record.
The component coordinate identities then identify both assembled maps
with the checked actual mate/unit/cap formulas of ActualMatrixFamilies.md.

unitMatrixComponentIso and capMatrixComponentIso, and their even-moving
counterparts, are isomorphisms of superspaces on old representables.
Their hom theorems identify the forward maps with the literal assembled
entry matrices. Their inv_even theorems prove that the actual inverses
preserve the specified parity grading. The two height profiles retain
the concrete degree equalities Q=S+m and S=Q+m.

This is representable component inversion at arbitrary endpoints over
the supplied commutative ring. Arbitrary-module bijectivity still
requires the graded kernel/coend realizations and source naturality;
it does not follow from the representable isomorphisms alone.
No such transfer is assumed here.

Strict producers and both concrete consumers pass. All forty-seven
component declarations and fourteen finite-superspace declarations are
audited. The connected mixed fixture covers both moving parities,
both height signs, and zero cap count. It checks each isomorphism's
literal forward matrix, inverse grading, and both inverse products,
with distinct mixed endpoint orders and positive cutoffs. Full CI
and the global audit remain integration gates.
