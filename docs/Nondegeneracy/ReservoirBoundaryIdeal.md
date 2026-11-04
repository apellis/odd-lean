# Off-window reservoir boundary membership

`ELVReservoirBoundaryIdeal` supplies SwappedHomInversion §4, condition (J),
for the literal chosen reservoir boundary. For a finite inverse slot j and
r>j, its reconstructed source coefficient has degree 2*d_i*(r-j)>0.
Realization puts it in the content coefficient grading; post-whiskering
with arbitrary surrounding maps lies in level one of the contentwise
jointly nilpotent coefficient ideal.

The eight public APIs are `positiveContent_mem_coeffGrading`,
`negativeContent_mem_coeffGrading`, `positiveContent_sandwich_mem`,
`negativeContent_sandwich_mem`, `positiveAction_evaluate_mem`,
`negativeAction_evaluate_mem`, `positiveNativeBoundary_evaluate_mem`, and
`negativeNativeBoundary_evaluate_mem` in `ReservoirBoundaries`.
The last two use the literal postcomposition chosen inverse-window
contractions. The negative absent unit window is retained through its
source degree theorem; it is not replaced by zero.

The producer and paired consumer pass strict pinned-toolchain checks,
including all 19 owned axiom audits. The consumer exercises every API,
both parities and height signs, every finite inverse slot and arbitrarily
large off-window rows, and an absent unit boundary whose diagonal acts
as identity on a proved nonzero odd-datum vacuum. No grading of arbitrary
Hom morphisms or uniform bound over an original-weight fibre is introduced.

Full integration and attachment to the padded reservoir entries remain
separate gates; the residual matrix inverse is not asserted here.
