# Invertible probe dots on global content induction

`ProbeGlobalDotInverse.lean` restricts the all-height signed dot inverse to the existing full content subcategories using `fullLiftTrans`. It then transports through the existing height/content identification. No action object is replaced.

`probeHeightContentDotIso` and `probeGlobalContentDotIso` prove both inverse products. The latter has the existing `globalContentDot` as its forward map, definitionally; `probeGlobalContentDotIso_hom` records that identification. The construction includes the vacuum boundary.

The producer and closed rational odd-colour vacuum and positive-content consumers passed strict direct Lean checks, including the owner axiom audit. Full build with warnings as errors, global axiom audit and concrete consumers passed before research integration in #807. This discharges the global action dot input of InvertibleDotProbe.md Section 5, equation (6). Comparison of the coefficient-specialized full action and prescribed inverse matrices, and fusion/nondegeneracy, remain separate.
