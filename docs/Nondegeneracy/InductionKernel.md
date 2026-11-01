# The Hom coefficient kernel of induction

The arbitrary-module step of
[DeformedMatrixComparison §4](DeformedMatrixComparison.md) tensors an
isomorphism of ordinary-right coefficient kernels with the input module.
[KernelTensor](KernelTensor.md) gives this quotient-level transport.
The resulting quotient must still be identified with the specified action.

`BalancedKernelTensor.inductionKernel J w` is the ordinary-right presheaf
with value Hom(Jv,w) at v and source action g ↦ J(a) ≫ g.
For every input functor M into super vector spaces,
`inductionKernelEquiv J M w` identifies its coefficient-kernel tensor
with the existing `BalancedInduction.Obj J M w`.

Both quotients use literally the same direct sum and balance relations,
so the equivalence is the identity. The forward and inverse tensor
formulas retain the entire input module factor. Specializing w to Jt
gives the underlying Res–Ind target kernel; no representable-only,
flatness or projectivity assumption is involved.

The strict source and concrete consumer pass, with all seven
owned-declaration axiom checks. The consumer uses the actual old append
functor and full-coefficient old representable, both even and odd moving
colours, both inverse products, the tensor formula and source
precomposition. Its mixed-crossing input has an odd coefficient from the
other colour and is proved nonzero at every sufficiently large cutoff.

Identification of the Ind–Res double-coend source kernel, finite-family
sums, the prescribed matrix kernel map and grading remain separate
obligations. Full CI is required before integration; see
[STATUS](STATUS.md).
