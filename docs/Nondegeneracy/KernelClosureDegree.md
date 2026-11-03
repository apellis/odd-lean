# Integer degree of represented unit-inverse-cap closures

This is the represented coefficient calculation needed by
[ReservoirClosureDegree](ReservoirClosureDegree.md), following the intrinsic
finite inverse calculation in [KernelMatrixInteger](KernelMatrixInteger.md).
It retains the prescribed ordinary unit/dot columns and ordinary dot/cap rows.

For old-category objects `v,t`, let `U_r` be
`actualUnitKernelComponent i r v t`, let `C_s` be
`actualCapKernelComponent i s v t`, and let `P` be the principal component
of the actual finite unit or cap matrix inverse in the applicable content
height range. The linear maps `positiveKernelClosure` and
`negativeKernelClosure` are exactly

\[
 b \longmapsto C_s(P(U_r(b))).
\]

If `b` has old-category integer degree `n`, the ordinary unit column has
degree `n+2d_i r`, the principal inverse adds `2d_i`, and the ordinary cap
row adds `2d_i s`. Thus both closures have degree

\[
 n+2d_i(r+s+1).
\]

`positiveKernelClosure_degree` and `negativeKernelClosure_degree` prove
this on the independently prescribed old Hom and balanced kernel degrees.
`kernelClosureDegree_pos` uses the positive symmetrizer to prove that the
shift is strictly positive for every pair of nonnegative powers. In
particular, identity input gives a coefficient of positive integer degree.
The coefficient may be zero; the argument uses homogeneity, not a
nonvanishing assertion.

The evaluation equations identify these maps on every OLD supermodule,
with an unrestricted module vector. The positive equation uses the actual
`moduleUnitColumn`, the principal coordinate of `moduleUnitMatrixIso.inv`
with its canonical source parity coordinate removed, and the actual
`moduleCapRow`. The negative equation uses `moduleCapMatrixIso.inv` on the
principal target insertion with its canonical target parity coordinate.
`negativeKernelCoordinates_single_tensor` identifies that insertion with
the raw upper-Hom coefficient inserted before the finite kernel tensor
coordinates. These comparisons use the represented inverse equations in
`ELVModuleInverseKernelCoordinates` and the prescribed entry evaluations;
no grading on arbitrary module Homs is introduced.

The paired consumer instantiates the formulas for the unequal symmetrizer
`(2,1)`, positive and negative content heights, height zero in either
orientation, every pair of dot powers, and represented module evaluation.
It audits every declaration owned by `ELVKernelClosureDegree` against the
repository axiom allowlist.

The chosen whole-weight reservoir closure still requires the chart
comparisons from its selected local inverse through the content and
weighted records to these OLD module formulas. The represented degree
calculation alone does not assert that final attachment or a source-central
coefficient witness for the chosen reservoir closure.
