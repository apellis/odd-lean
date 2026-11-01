# Shifted unit-family component coordinates

DeformedMatrixComparison (6), together with the unit-column parity profile
in section 4 and Brundan--Ellis equations (1.13)--(1.14), requires explicit
coordinate units when the ordinary unit/dot columns are left unscaled.

ELVUnitFamilyCoordinates constructs the unitCoefficientDiagonal from
the units d_r = sign(r(r-1)/2 times the moving parity), and proves
unitDotPolynomialMap_diagonal: applying the normalized polynomial map
after this diagonal gives the finite sum of ordinary, unscaled
adjunction-unit/induction-dot columns. No field hypothesis is used.

unitFamilyPlainCoordinates uses the canonical module parity isomorphisms
on the actual finite source family Pi^p(Ind Res M) and Pi^(r p)M.
For odd moving colour, unitFamilyComponentEquiv then combines these
coordinates, the explicit diagonal units, the literal polynomial window,
and the checked ordinary-source positive inverse. Its forward formula
has the signed balanced crossing in the first slot and the unscaled
ordinary unit/dot columns in every remaining slot.

The equivalence is componentwise for old representable modules, arbitrary
old endpoints and the supplied commutative ground ring, with the concrete
height equality Q = S + m. The first coordinate is explicitly -tau J:
identifying that coordinate with the ordered mate remains an obligation.
No inverse of the actual module matrix is asserted before that comparison
and naturality are established. Integer grading is outside this SVec model.

The producer and concrete consumer pass scoped builds with warnings as
errors. The mixed connected fixture has distinct endpoint orders,
positive cutoffs, three unit summands, both inverse identities, the whole
forward formula, and a nontrivial d_2 = -1 coordinate. All twenty-two
owned declarations pass the consumer axiom audit. Full CI and the global
audit remain integration gates.
