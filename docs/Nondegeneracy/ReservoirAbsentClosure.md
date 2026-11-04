# Reservoir closure at an absent predecessor

This is the absent-predecessor branch of the source-coefficient calculation
in [ReservoirClosureDegree](ReservoirClosureDegree.md). It concerns the
literal closures selected by `elvRouquierFamily`, including the principal
entry chosen by its local inverse record.

Fix adjacent steps `x₀+αᵢ=x₁` and `x₁+αᵢ=x₂`, and an output content
block `δ` at `x₁`. Assume precisely that there is no block `β` at `x₀`
whose successor is `δ`. This is the formal-content condition

```text
¬ ∃ β, blockSucc D Λ i h₁ β = δ.
```

The lower induction component at `δ`, applied to the restricted input, is
zero by `elvInductionComponent_isZero`. The chosen lower counit therefore
has zero component there. Expanding the total of the closure composition
shows that its final factor is zero. Neither the dot powers nor the
principal inverse need to be unfolded or compared.

`ReservoirClosures.positive_total_absent` and
`ReservoirClosures.negative_total_absent` prove, in their respective height
ranges, that the actual whole-weight closure has component zero on every
input family and every pair of dot powers. The hypotheses contain no
vanishing assumption on the input or on its output-content module. The
argument retains formal content and does not infer a unique content from
an equality of weights.

The paired consumer checks a connected asymmetric Cartan datum with an
even and an odd colour. It exercises both inverse orientations at height
zero and the negative orientation on an absent-colour block with positive
other-colour content and strictly negative categorical height. Every owned
declaration is audited against the standard axiom allowlist.

The producer and paired consumer pass strict scoped checking with Lean 4.34.1,
warnings as errors and both prescribed transparency compatibility options.
Both owned declarations pass the standard axiom allowlist audit.
Full package CI remains the integration gate.
