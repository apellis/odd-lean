# Actual shifted coefficient source

The proposed component-level linear equivalence is
`shiftedSourceCanonicalEquiv` in `ELVShiftedSourceLinearEquiv.lean`.
Its forward map is the total component of the fixed actual module isomorphism,
followed by `coefficientOneSourceEquiv`; the inverse uses the actual inverse
component. Both inverse products and the original adjunction counit square
are retained. This new component construction is unverified pending CI.
Higher dotted-row conversion must account for the odd source isomorphism's
anticommutation sign; the zeroth counit square alone does not fix higher rows.


Status: proposed Lean implementation; full CI pending. Target: DeformedMatrixComparison (3), (5).

ELVOldAppendSuperfunctor equips the existing old append with its full coefficient superfunctor structure, using even affine right-whiskering and tensor parity. ELVShiftedCoefficientComparison identifies the prescribed coefficient(1) projection and action with actual parity-shifted restriction of oldRepresentable. The comparison is identity on quotient coefficients and even on independently specified gradings.

ELVShiftedCoefficientModule packages that same coefficient functor as its actual supermodule, induces the even module isomorphism, and composes it with canonical parity source transport. The induced carrier is literally the prescribed odd Source after the supplied parity equality. The actual counit after canonical transport equals the original actual counit.

Still required: coefficientwise evaluation of the whole shifted counit against the concrete input contraction, higher dot normalization, coefficient truncation and exact-content transport, and the final categorical matrix comparison. No arbitrary source isomorphism, faithful model, flatness premise, completed action or nondegeneracy theorem is claimed.
