# Actual append-corner last-dot inverse

The probe algebra and existing induction action explicitly assume a finite colour type. `ProbeAppendDotInverse.lean` retains this hypothesis and sums inverses over Word I (n+1), a finite type under that assumption. It makes no assertion that words are finite in number for arbitrary colours.

The source identifies the existing inductionLastDot with the actual last-position dot, assembles the finite word-corner inverses, proves both products equal the genuine append idempotent, and projects the inverse into its literal corner. This is the actual algebraic input for the signed-right induction-dot inverse.

This is source in progress until full CI passes. Its next obligation is the inverse as a homogeneous superbimodule map and supernatural transformation, with the odd inverse's required extra parity sign. No full-action matrix comparison follows merely from the append-corner unit.
