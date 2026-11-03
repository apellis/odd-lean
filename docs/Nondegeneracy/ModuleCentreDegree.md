# Represented degree reconstructs a source coefficient

[ELVModuleCentreDegree](../../OddMath/QuiverHecke/CyclotomicAction/ELVModuleCentreDegree.lean)
connects the represented degree target in
[ReservoirClosureDegree](ReservoirClosureDegree.md) to the existing source
coefficient grading. It uses `ModuleCentre.reconstruct`, rather than adding
another reconstruction of the supercentre.

`reconstruct_app_evaluate` identifies each parity component of the recovered
source coefficient at `v` with `ModuleYoneda.evaluate` of the original
module-centre component on the representable at `v`. The component is
homogeneous in parity, so its total evaluation is its specified parity
component. The existing reconstruction retains the total-parity twist;
no evenness assumption or sign suppression enters this identity.

`reconstruct_mem_degree_iff` says that the recovered coefficient has integer
degree `d` exactly when all these represented evaluations, for every source
object and both parities, lie in `truncatedDegree ... d`.
`exists_coefficient_of_represented_degree` supplies the resulting source
coefficient, its degree membership, and equality of its realization with
the original natural transformation on all exact-content modules.
These statements work over any ordinary commutative ring, without an
invertibility-of-two hypothesis. The symmetrizer and parameter homogeneity
are the hypotheses already required by the source integer grading.

The [consumer](../../scripts/NonVacuity/ELVModuleCentreDegree.lean) constructs
rank-one odd data over the rationals at cutoff two, coefficient cutoff
three, and positive one-strand content. The source identity coefficient
and its module-centre realization are both proved nonzero using the
surviving odd exterior class `truncatedSingle ... delta 0`. Its represented
degree-zero input is independently proved from the existing source
identity degree, for every representable and both parities, and the new
existence and degree-criterion theorems are applied to that concrete input.
The fixture tests reconstruction and degree transport; it does not prove
the positive degree of the intended inverse-defined reservoir closure.

For that closure, the remaining input is its actual exact-content natural
transformation and the represented degree computation
`2 * sy.d i * (r + s + 1)` for its selected unit, dots, principal inverse,
and counit. Feeding that computation into the existence theorem produces
the coefficient witness required by the existing coefficient ideal.
No integer grading on arbitrary module morphisms is introduced, and the
represented degree hypothesis is an intermediate lemma to discharge.

Both isolated checks use strict warnings and the repository compatibility
flags. The owned audit covers three declarations with only the standard
allowed axioms.
