# Tensor vacuum functor

SwappedVacuumCoordinates requires an occupied functor from probe modules
to reservoir modules. `VacuumTensor.superfunctor W a` sends M to the module
with values W(c) tensor M(a). Reservoir arrows act on the first factor;
input supernatural transformations act on the second with the Koszul sign.
The complete generic producer passes strict checking with default limits.

This source-only checkpoint is unexported. The actual probe/reservoir Pi-category specialization and its component
Koszul formulas also pass strict checking. Its regular-vacuum identification
and occupied paired consumer remain to be supplied. No complete mixed-entry evaluation is claimed.
