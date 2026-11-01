# Tensoring many-object coefficient kernels

The kernel tensor step of [DeformedMatrixComparison](DeformedMatrixComparison.md), section 4, requires an inverse on arbitrary modules. The component inverses on representables do not by themselves supply that conclusion, and no colimit in the category of all supernatural module maps is assumed.

The proposed [ELVKernelTensor](../../OddMath/QuiverHecke/CyclotomicAction/ELVKernelTensor.lean) constructs the explicit ordinary-right tensor quotient for a presheaf K on the source category and a covariant supermodule M. Its relations are

    K(a)(x) tensor m = x tensor M(a)(m).

The kernel map descends precisely by source naturality. A natural isomorphism K ≅ L induces BalancedKernelTensor.equiv M e, with its inverse descended from e.inv and both identities checked on quotient tensors. The helper coefficientIso derives inverse naturality from bijectivity of the forward natural map at each coefficient object; equivOfBijective then tensors that isomorphism. No flatness, projectivity, finite-dimensionality or categorical cocompleteness is required. The concrete consumer swaps two rational coefficient coordinates while retaining an old quotient representable as its module, checks bijectivity and applies balance to an arbitrary old arrow.

The producer and concrete consumer passed strict local checking, including the audit of all owned declarations. Repository CI remains the integration gate. This is the underlying ground-ring equivalence only. Grading preservation, actual EF/FE kernel identifications, finite shifted sum comparisons, and attachment of the prescribed matrix remain necessary downstream. ModuleYoneda.fromElement and ContentYoneda.fromArrow already provide the signed representable arrows; their total-parity twists must be included before presenting ordinary-right actions. The existing content ring modules do not supply a proved equivalence between content supermodules and ring modules.
