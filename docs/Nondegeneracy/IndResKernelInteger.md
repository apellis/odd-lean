# Integer degree on the represented lower-loop kernel

For a graded append functor `J : C ⥤ D`, the existing represented
induction-restriction coefficient kernel is the literal balanced quotient
of

    ⨁ s, Hom_D(Js,t) ⊗ Hom_D(v,Js).

`IndResKernel.integerDegree` defines its degree `n` intrinsically as
the sum of images of tensors with total Hom degree `n`.
`integerDegree_internal` proves these parts form an internal direct sum.
The grading is not transported through the finite forward matrix or its
inverse.

`integerProjection` descends the ordinary graded tensor-product
projection through the actual balance relations. Balancing is checked
against every source arrow by decomposing the source arrow and both Hom
factors into their homogeneous parts. On such tensors,
`integerProjection_tensor` selects exactly the sum degree.
`integerProjection_mem` and `mem_integerDegree_iff_projection` identify
its image with the intrinsic degree part. The original quotient and
all its inhomogeneous vectors remain present.

This supplies the represented-kernel grading needed in
`ReservoirClosureDegree.md`; it makes no integer-grading assertion for
arbitrary maps between ungraded modules. For the concrete old ELV
category the required graded append is constructed by
`ELVOldCategoryGrading` from the actual symmetrizer and homogeneous
parameters. The chosen dot and equal crossing have their independently
proved degrees in `ELVOldGeneratorDegrees`.

The paired consumer uses asymmetric rational parameters with two odd
colours and symmetrizer `(2,1)`, a mixed word, both chosen append
functors, identity tensors and the actual appended-dot tensors, all
projection degrees, the internal decomposition, and projection range
and membership characterizations.
