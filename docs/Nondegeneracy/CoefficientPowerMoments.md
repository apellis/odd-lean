# Higher moments on the literal coefficient-power vacuum

This attaches the one-strand coefficient-extraction input of
[SwappedVacuumNonpositiveBubbles, §§2–4](SwappedVacuumNonpositiveBubbles.md)
to the actual regular A/T old vacuum.
`ELVCoefficientPowerMoments` and its paired occupied consumer pass scoped
Lean checks with warnings as errors and both pinned compatibility settings.
All 24 owned declarations pass the standard axiom allowlist audit. Full CI
remains the integration gate.

Use the actual vacuum M, its original even empty-component equivalence
E from A/T and the prescribed last inverse row λ of
[CoefficientPowerRows](CoefficientPowerRows.md). For a literal one-strand
old arrow f, `rawVector` is the balanced tensor f⊗E(1). The linear map
`upperFunctional` applies λ to this tensor. `rawMoment(a,n)` evaluates
this map on the full coefficient-left raw class [a t^n]. No evaluation
kernel, annihilating polynomial or coefficient functional is a premise.

`rawMoment_recurrence` applies this map to `single_recurrence`, the actual
old one-strand relation, with the original products a*c_j. The monic
leading coefficient gives `rawMoment_leading`, a terminating recurrence
whose remaining dot exponents are strictly smaller than N+m.

`rawMoment_coefficient` uses the actual output-endomorphism naturality of
λ. An arrow [t^n] followed by the appended coefficient arrow is exactly
[a t^n]. Thus, for a of parity q,

    μ(a,n) = (−1)^((N−1)p_i q) [a] μ(1,n).

Multiplication here is the original left multiplication in literal A/T.
The proof does not replace odd coefficients by commuting scalars.

`signedMoment(n)` applies λ to the actual signed induction-dot power
D^n followed by the ordinary unit on 1. At every exponent,
`signedMoment_rawMoment` and its inverse prove

    K_n = σ_n μ(1,n),    μ(1,n) = σ_n K_n,
    σ_n = (−1)^(binom(n,2) p_i).

This uses the existing all-module signed-dot iteration on the actual
unit tensor. No extra cap rescaling occurs. The prescribed inverse-row
window gives `rawMoment_one_window` and `rawMoment_window` for all
n<N, including odd coefficient classes.

`rawMoment_one_recurrence` and `signedMoment_recurrence` consequently
express the actual monic relation entirely in these scalar A/T-valued
moments, retaining both the top-row coefficient sign and triangular
signed-power scalar at every exponent.

The connected asymmetric two-odd-colour consumer takes N=2 and squares
of the even elementary generators. Both independent odd coefficient
classes survive in the actual power quotient. The coefficient of t in
the literal monic relation is δ_i. The raw low window and leading solve
therefore prove

    μ(1,2) = [δ_i],    K_2 = −[δ_i] ≠ 0.

This is the first moment above the extraction window, derived from the
actual old relation. The consumer also instantiates the complete higher
signed recurrence on this occupied vacuum.

The complete ordinary remainder series is derived from these moments in
[CoefficientPowerRemainders](CoefficientPowerRemainders.md), with its exact
all-exponent signed normalization. Identifying the mixed inverse caps and
the final swapped vacuum's bubbles with these maps is still required. No all-height bubble theorem or vacuum evaluation-kernel
identity is asserted.
