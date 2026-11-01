# Low polynomial and reversed cap coordinates

The finite cap coordinates in DeformedRouquierMatrix, section 4, are shared
by both moving parities. LowPolynomialCoordinates extracts the existing
module-generic finite-vector/low-supported-polynomial equivalence and
coordinate reversal from the odd input matrix. The odd matrix imports and
uses those same declarations; its public input inverse API is preserved.

lowVectorEquiv identifies Fin(m)-indexed coefficient vectors with
polynomials supported below m. lowVectorEquiv_single identifies each basis
column with its literal Finsupp.single. reversedVector and
reversedVector_single implement the anti-diagonal coordinate reversal
before finite triangular elimination.

The independent integer-coefficient consumer and the existing odd input
matrix consumer pass scoped builds with warnings as errors. The independent
consumer audits all seventeen owned declarations. Full CI and the global
audit remain integration gates. The even cap matrix uses the same
coordinates and the existing finite triangular elimination theorem.
