# Homogeneous transformations on iterated induction

DeformedMatrixComparison (2), (4) and DeformedActionAssembly §§5–6 use the
literal equal-colour two-letter crossing conjugated by the chosen
induction-composition isomorphism. `doubleTransformLinear` is that conjugate
on the literal iterated coends, for arbitrary successive functors between
three categories and an arbitrary homogeneous endotransformation of their
composite.

`doubleTransformLinear_tensor` flattens a nested generator with coefficient
`K.map a ≫ g`, applies the transformation with the full parity twist on that
coefficient, and unflattens with the canonical unit tensor in the first
factor. It introduces no homogeneity assumption on either coefficient arrow.
`doubleTransformLinear_eq_total` identifies this literal coend operator with
the total component of the given homogeneous module transformation
conjugated by the two chosen induction flattenings. `doubleHom_ext` reduces
equality of linear operators on iterated induction to these nested tensors.

The paired consumer uses the given old fixed-content equal-colour crossing
on connected mixed scalar probe regular modules, both moving colours,
arbitrary nested coefficient arrows and vectors, and vacuum unit tensors.
The transform computation is separate from proving that a selected scalar
comparison intertwines the old and ordinary operators. In particular,
normalized cap rows are not identified with unshifted counits here.
