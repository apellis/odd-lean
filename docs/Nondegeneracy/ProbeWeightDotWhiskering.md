# The two chosen global OLD probe dots

`probeOldOuterDot_component` and `probeOldInnerDot_component` compare the independently whiskered global signed dots to the actual two chosen block inductions. Both use exactly `probeOldWeightPair_obj_eq`, the same supported coordinate equality used by the global equal crossing. The outer formula retains the chosen outer block dot at the true induced input; the inner formula retains the ordinary chosen outer induction map of the chosen inner block dot.

These identities are for every parity component and every scalar-evaluated input module. The producer and paired consumer pass strict scoped verification with warnings as errors and both compatibility settings. All four owned declarations pass the standard axiom audit. Full package integration remains separate. The consumer tests both moving parities, nonempty mixed contents, and the parity-shifted regular vacuum. These comparison identities are the transport inputs for both global signed nilHecke slides; they do not themselves assert those slides.

The source head `2652d0a76a9ee31ee3c669eb1ad35736b837fee4` passed the
full build, global axiom audit and all concrete consumers in
[#1014](https://github.com/apellis/odd-lean/pull/1014)
([CI run](https://github.com/apellis/odd-lean/actions/runs/41691819623)),
merged at `2c1306c4`.

The common proof now covers arbitrary colour pairs.
`probeOldWeightPair₂_obj_eq` retains both chosen colours in the selected
product coordinate; `probeOldPairOuterDot_component` and
`probeOldPairInnerDot_component` identify the two independent dots there.
The original equal-colour statements are unchanged specializations.
The generalized producer and extended mixed/shifted regular-probe
consumer pass strict checks, auditing all seven owned declarations.
Full integration of this extension remains separate from #1014, which
verified the earlier equal-colour source.
