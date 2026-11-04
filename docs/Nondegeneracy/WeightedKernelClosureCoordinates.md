# Weighted local closures and represented kernel closures

The inverse degree step G8 requires the prescribed unit–principal-inverse–cap closure, rather than a separately selected inverse. `weightedContentUnitClosureValue` and `weightedContentCapClosureValue` are the literal weighted ordinary unit/dot column, the existing local record's principal inverse, and the ordinary dot/cap row, evaluated on one content object.

Their `_atWord` equations identify these closures with the action of `positiveKernelClosure` or `negativeKernelClosure` on the identity coefficient. The input module vector is arbitrary; no integer grading on that module is assumed.

The comparison first evaluates the given local inverse record as the exact finite inverse's principal row or column. The selected weighted and parity charts identify that principal with the chosen OLD inverse. The checked ordinary unit/cap chart equations and the raw kernel tensor inverse equations then identify the whole closure. The raw coefficient endomorphism is the same one whose integer degree is `2 dᵢ (r+s+1)` in `ELVKernelClosureDegree`.

The producer and paired consumer pass strict scoped checking with Lean 4.34.1,
warnings as errors and both prescribed transparency compatibility options.
The consumer covers both moving parities, both height orientations and empty
finite windows, retains an independently detected nonzero weighted inverse
value, and audits all 28 owned declarations against the standard axiom
allowlist. Full package CI remains the integration gate.
