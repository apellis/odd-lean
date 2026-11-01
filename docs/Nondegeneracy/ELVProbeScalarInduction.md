# Old append induction preserves scalar coefficient evaluation

`ELVProbeScalarInduction.lean` proves that the actual balanced induction
along the canonical untruncated old content append preserves
`ProbeEvaluatesCoefficients`. The proof uses the complete coefficient
slide, including its output parity twist, followed by the existing coend
balance. Even coefficients retain their scalar; odd coefficients have
zero scalar evaluation and vanish. No flatness premise or PBW
decomposition occurs, and the theorem does not require finitely many colours.

The actual probe module satisfies the input condition by
`probeOldModule_evaluatesCoefficients`, so this is a concrete preservation
result rather than a new assumed action comparison.

Strict local producer and all closed consumers pass; all 18 owned
declarations pass the axiom audit. Mixed odd/even consumers check both
append parities, an odd coefficient from another colour after an even
append, and the prescribed nonzero elementary scalar after odd append.
Full CI remains the integration gate.

This closes the scalar-kernel preservation input. The coend comparison with
the ordinary height induction and prescribed inverse-matrix comparison
remain separate. The source is untruncated throughout.
