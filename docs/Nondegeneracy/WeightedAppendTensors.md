# Tensor generators of weighted append comparison

DeformedActionAssembly §§5–6 and STATUS critical-chain item 2 require
the selected comparison between old append induction followed by weighted
descent and append induction in the truncated category to preserve the
chosen diagram generators.

`BalancedInduction.squareComparison` computes the middle four maps of
this comparison for an arbitrary commuting square of superfunctors. Its
`squareComparison_total_tensor` retains the exact equality transport at the
source of the arrow. The induced input map is assumed even in this intermediate
calculation; the application uses the actual even quotient-induction counit.
Neither arrows nor module vectors are assumed homogeneous.

`weightedAppendComparisonLinear` is exactly the chosen
`appendWeightedModuleIso.hom.total`, expressed on the literal old and
truncated balanced coends. `appendWeightedModuleIso_hom_tensor` specializes this
calculation to the literal append/quotient square, after the established formula
for the inverse quotient/descent comparison. It asserts that the chosen
five-isomorphism comparison sends `[g ⊗ b]` to `[Q(g) ⊗ b]`. The object transport
in the commuting square is the identity; the quotient-induction counit on its
unit tensor is the identity on the input vector. Its
`appendWeightedModuleIso_hom_unit` is the corresponding unit formula.

The paired examples instantiate both moving parities on mixed and vacuum
truncated representables and allow arbitrary old output arrows. They audit every
declaration owned by the new producer. The producer and mixed/vacuum
consumer pass strict scoped compilation with the pinned toolchain and both
compatibility settings; all 32 owned declarations have allowed axioms.
Full CI is pending. Chosen dot, crossing and ordinary adjunction compatibility remain separate;
assembling normalized content and weight functors is not asserted here.
