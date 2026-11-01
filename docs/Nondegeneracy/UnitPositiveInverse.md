# Ordinary-source positive inverse

DeformedMatrixComparison (4) transfers the nonnegative-height inverse
of DeformedRouquierMatrix, section 4, to the ordinary induction-restriction
carrier and the ordinary unit/dot columns.

unitPositiveMatrixEquiv precomposes the existing raw positive inverse with
the canonical source equivalence, followed by crossing-source negation.
The polynomial complement uses the literal low coefficient window.
unitPositiveMatrixEquiv_apply proves that its forward value is exactly
-toCyclotomic(Jz) + unitDotPolynomialMap(r).
The latter is the scalar-normalized finite assembly of actual adjunction
unit and ordinary induction-dot powers, as proved in UnitDotColumns.md.
There is no assumed source comparison, unit/dot equality or matrix inverse,
and no coefficient elimination is repeated.

Scope is odd moving colour, arbitrary old endpoints and the supplied
commutative coefficient ring, under outputSDegree≤endpointQPDegree.
The producer and mixed concrete consumer pass scoped builds with warnings
as errors. The consumer uses distinct endpoint orders, positive cutoffs,
both inverse identities and the complete forward formula. All seven owned
declarations pass its audit. Full CI and the global audit remain required.

The first component is explicitly -toCyclotomic after the canonical J.
Identifying it with the ordered categorical mate and packaging the full
parity-shifted module summand family remain separate.
