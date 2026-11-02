# Selected iterated scalar append comparison: proposed calculation

The double-induction crossing in DeformedActionAssembly §§5–6 and
DeformedMatrixComparison (2), (4) uses the prescribed one-letter append
comparisons. The proposed `probeDoubleAppendOrdinaryModuleIso` first applies
the selected comparison for the outer append, then induces the selected
inner comparison. Its source is the literal descent of iterated old
induction; its target is iterated ordinary induction.

The proposed `probeDoubleAppendComparisonLinear` computes this composite on
literal coends. The intended `probeDoubleAppendOrdinaryModuleIso_hom_tensor`
sends nested old tensors to their two ordinary quotient tensors, preserving
the order of arbitrary coefficient arrows. The calculation is being
reencoded with an independent intermediate old module before specializing
to the first induction. The selected isomorphism definition elaborates;
the tensor and selected-total boundary are not yet jointly verified. No
composite parity theorem is claimed.

`ELVInductionDoubleTransform` proposes the canonical flattening-conjugated
homogeneous transform on literal nested coends and its tensor formula. Its
first check encounters an elaboration timeout at the linear-composition
rewrite; it is not a checked result. The paired proposed consumers use the
connected mixed scalar probe regular modules, arbitrary coefficient arrows,
and vacuum. They have not yet passed against the proposed producers.

This is an unfinished source snapshot. The scalar crossing coefficient
image and canonical raw composite-square crossing theorem are checked in
the separate `ProbeAppendCrossing` note. Attaching that calculation to the
selected iterated comparison and both induction flattenings remains open,
including the prescribed extra minus. Normalized cap rows remain distinct
from the unshifted counit.
