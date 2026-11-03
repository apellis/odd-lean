# Weighted matrix chart and row comparison

DeformedMatrixComparison (2), (4) compares the prescribed arbitrary-module
old matrices with the weighted quotient matrices in canonical parity
coordinates.

`ELVWeightedMatrixInverse` constructs `weightedUnitFamilyValueEquiv` and
`weightedCapFamilyValueEquiv` from the selected append source/target charts
and the actual module parity isomorphisms. Their finite products are
`weightedUnitMatrixValueEquiv` and `weightedCapMatrixValueEquiv`.

`weightedUnitColumnValue_compare` and `weightedCapRowValue_compare` attach
all powers of the given ordinary unit/dot and dot/counit rows to those
charts. `weightedMateTotalValue_compare` attaches the actual first mate
component, with its original crossing and minus sign. The native value
comparison and raw field bindings keep the selected maps throughout.

`weightedModuleUnitMatrixIso` and `weightedModuleCapMatrixIso` conjugate the
given old matrix isomorphisms by these finite coordinate equivalences,
under the actual content height hypotheses. They provide isomorphisms of
the weighted matrix spaces; no inverse or flatness hypothesis is supplied.
Their forward identification with `weightedUnitMatrixComponent` and
`weightedCapMatrixComponent` remains open. This file therefore does not yet
prove that the prescribed weighted forward matrices are invertible.

The producer and paired mixed-colour, positive-height, negative-height and
vacuum consumer pass the pinned strict checks, including the allowlist
audit of all owned declarations. The next step is the finite parity entry
squares and assembly of the forward matrix comparison.
