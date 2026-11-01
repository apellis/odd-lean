# Coefficient-kernel entries on arbitrary supermodules

DeformedMatrixComparison §4 requires the kernel inverse to recover the
prescribed categorical matrix. The coefficient source action is ordinary
precomposition on all arrows. On an arbitrary supermodule M, evaluate a
coefficient tensor [g ⊗ b] against m by [g ⊗ M(b)m].

`actualMateKernel_evaluate_tensor` proves that this evaluation takes the
fixed signed kernel mate to `matrixMateComponent M`. The proof retains
the ordered equal crossing and whole parity twist, uses the established
ordinary module mate tensor formula, then balances by b.
`kernelMateEvaluation` and `moduleMateEvaluation` freeze the literal
quotient endpoints; `actualMateKernel_evaluate` proves their equality on
all coefficients by the balanced universal property.

`actualDotKernel_evaluate` and `actualCounitKernel_evaluate` intertwine
evaluation with the actual induction dot and ordinary counit. The former
gives every power by semiconjugacy. Consequently
`actualCapKernel_evaluate_moduleCapRow` identifies every row with the
literal `moduleCapRow M n`.
`actualUnitKernel_evaluate` identifies the unscaled ordinary unit/dot
column with `moduleUnitColumn M n`, retaining its prescribed odd
dot-power scalar. No representable-density, coefficient flatness or
homogeneity assumption on the input coefficient or vector is used.

The producer and paired concrete consumer pass strict source checks;
all24 owned declarations pass the axiom audit. The consumer applies
both moving parities and every dot power to the actual mixed old
representable module, and proves that its source coefficient coend
vectors survive every sufficiently large cutoff through their ordinary
counit image with a nonzero exterior coefficient.

The remaining matrix assembly must compose the IndRes, Hom and finite-family
quotient equivalences with the canonical parity coordinates, and use these
entry identities to identify the whole forward map. Pointwise coefficient
bijectivity and all-module matrix evenness are separate proved inputs.
Full exact-head CI is required before integration.
