# Actual shifted finite matrix component inverses

DeformedMatrixComparison section 4 and Brundan--Ellis (1.13)--(1.14)
use the fixed ordered categorical mate, ordinary dotted units or
counits, and the canonical finite parity-shifted families.
ELVActualMatrixFamilies attaches the actual mate first-row theorems
to the checked component inverses in both moving parities and both
height signs.

matrixMateRow is the specified p-component of oldModuleMate, evaluated
under the canonical upper-Hom equivalence with a literal Old quotient
codomain. matrixMateRow_apply and matrixMateRow_even_apply prove its
signed crossing normalization using the fixed canonical odd or even
source comparison. There is no chosen mate, source equivalence or
normalization premise.

unitFamilyComponentEquiv_actual and its even counterpart identify
the complete positive component map with that actual mate row and the
ordinary unscaled unit/dot columns, in the canonical source parity
coordinates. capFamilyComponentEquiv_actual and its even counterpart
identify the negative map with the same actual mate row and the literal
moduleCapRow components, in the canonical target coordinates. The
existing equivalences supply both inverse identities; no elimination
is repeated. The module entry comparisons are in MatrixEntryTotals.md.

These are representable component results for arbitrary old endpoints
over the supplied commutative ring, under the actual degree/height
equalities. Passing to arbitrary modules requires the coend/kernel
realizations and input naturality, including the prescribed parity
shifts. That remaining transfer is not supplied by representable
component inversion alone and is not asserted here.

The strict scoped producer and concrete consumer pass; all ten owned
declarations are audited. One connected mixed asymmetric datum tests
all four parity/height cases, with distinct endpoint orders and positive
cutoffs. Unit windows have six and four slots; cap windows each have
three. Every case checks both inverse products and the complete actual
mate/unit/cap forward formula. Full CI and the global audit remain
integration gates.
