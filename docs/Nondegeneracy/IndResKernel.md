# The induction-restriction kernel on arbitrary modules

This is the explicit double-balanced-tensor step required by [DeformedMatrixComparison](DeformedMatrixComparison.md), section 4. For a functor J:C→D, define the coefficient kernel

    U_t(v) = integral_s Hom(Js,t) tensor Hom(v,Js).

Its ordinary-right action is precomposition in the second factor. Tensoring U_t with an arbitrary D-module M identifies with the existing balanced induction of the restriction of M. The proposed equivalence is IndResKernel.equiv J M t in [ELVIndResKernel](../../OddMath/QuiverHecke/CyclotomicAction/ELVIndResKernel.lean).

The forward map sends [(g tensor b) tensor m] to [g tensor M(b)m]. The inverse sends [g tensor m] to [(g tensor id_Js) tensor m]. Inner balance proves the inverse is well defined; outer balance proves the second roundtrip. Both quotients are the existing ground-ring direct sums modulo explicitly generated submodules. No exactness, projectivity, flatness or categorical colimit is used.

The producer and concrete old-quotient consumer passed strict local checking, including the audit of every owned declaration. Repository CI remains the integration gate. This is the underlying ordinary-right kernel realization, not grading transport or a prescribed matrix inverse. The source action intentionally uses ordinary precomposition; signed representable transformations require the additional twists recorded in [KernelTensor](KernelTensor.md).
