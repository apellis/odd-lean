# The selected iterated scalar append comparison

The double-induction crossing in DeformedActionAssembly §§5–6 and
DeformedMatrixComparison (2), (4) uses the prescribed one-letter append
comparisons. `probeDoubleAppendOrdinaryModuleIso` first applies the selected
comparison for the outer append, then induces the selected inner comparison.
Its source is the literal descent of iterated old induction; its target is
iterated ordinary induction.

`probeMappedAppendIso` and `probeMappedAppendLinear` isolate this calculation
for an independent intermediate old scalar-evaluated module and an ordinary
module isomorphism. `probeMappedAppendLinear_eq` identifies the raw linear
map with the selected composite's total component.
`probeMappedAppendLinear_tensor` computes an outer tensor when the inner
isomorphism is even. This is an intermediate comparison lemma; the chosen
single-letter scalar isomorphism discharges its evenness hypothesis.

`probeDoubleAppendComparisonLinear` specializes that literal linear map to
the first old induction. `probeDoubleAppendComparisonLinear_eq` identifies
the same specialization with the chosen module isomorphism's total map.
`probeDoubleAppendOrdinaryModuleIso_hom_tensor` sends nested old tensors to
their two ordinary quotient tensors, preserving the order of arbitrary
coefficient arrows. The theorem writes the computed mapped-append expression
on the left, definitionally the named double-comparison linear map, to keep
its literal coend endpoints aligned.

The producer and connected mixed/vacuum consumer pass strict pinned checks,
including the owned-declaration axiom audit. Both colours and arbitrary
coefficient arrows and vectors are included. No composite parity theorem is
asserted. The separate `InductionDoubleTransform` note supplies the chosen
flattening conjugates. Intertwining the selected scalar comparison with
those crossing operators remains a separate obligation, with the prescribed
extra minus. Normalized cap rows remain distinct from unshifted counits.
