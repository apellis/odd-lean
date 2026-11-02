# Dotted mate of the raw coefficient

Current scope and verification are maintained in [STATUS](STATUS.md). Any original
topic-head pending checks below are historical; they do not override the consolidated
status or establish completion of the full conjecture.

The raw arbitrary-input coefficient is now specialized to the input
`ΠH≫F` used by the dotted mate. Every shift and operator uses the same
existing post-induction Π-Hom witness as the raw constructor; no equality
between differently packaged coefficient choices is assumed.

The existing generic `mixedOddNorms` proof is exposed publicly, unchanged.
Its arbitrary module-valued input functor and componentwise bounds are
independent of Hom parity-shift witness names. Applying it to the literal
chosen transpose gives both source norms under the raw constructor's witness.
The actual raw coefficient's proved inverse identity and target norm then
supply the generic dotted-mate criterion directly.

The module supplies these odd source norms and invertibility of
the prescribed dotted mate of `elvRawMixedCoefficient`. The arbitrary-Z
constructor and its normalization are unchanged. Existing odd probe/full-ELV
consumers at probe degree6 with both Hom shifts nontrivial pass strict local
checks. Both new declarations are axiom-audited against propext, Classical.choice,
and Quot.sound. The visibility/doc-only edit to ELVMixedSourceOddNorms and its
original consumer also pass strict checking and the all-9-owned audit. Full CI
is the integration gate.
