# Probe append-corner last-dot inverses

The existing probe algebra and induction action assume a finite colour type. `ProbeAppendDotInverse.lean` retains this hypothesis and sums inverses over Word I (n+1), proving both products equal the append idempotent in the literal cyclotomic corner.

`ProbeHeightDotInverse.lean` makes the same construction uniformly over Word I n for the existing all-height action. At n=0 this is the unique empty word, whose appended one-strand dot is a unit by the defining probe relation. Thus the vacuum needs no new induction functor.

Both producers passed strict direct Lean checks. The signed homogeneous superbimodule and supernatural inverse is supplied by ProbeSuperDotInverse.lean, including the odd extra parity sign. Full branch CI remains the integration gate. Coefficient-specialized comparison of the entire action and prescribed inverse matrices is separate.
