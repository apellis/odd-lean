# Finite superspace matrix coordinates

The finite sums in Brundan--Ellis (1.13)--(1.14) use the pointwise
superspace grading on their coordinate families.
OddMath.Algebra.FiniteSuperspace constructs this grading, identifies
its homogeneous parts componentwise, and assembles specified columns
and rows. Even entries give even assembled maps. No dimension, field,
or characteristic hypothesis is added.

This helper is used by FiniteMatrixComponents.md on the actual shifted
module families. Its strict producer and concrete integer-ring consumer
pass, with all fourteen owned declarations audited. The consumer has
nonzero even and odd parts, a nonzero odd family, explicit column sum,
and even row/column assembly. Full CI and the global audit remain required.
