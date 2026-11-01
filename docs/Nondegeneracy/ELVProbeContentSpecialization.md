# Scalar specialization of the untruncated ELV content ring

`ELVProbeContentSpecialization.lean` constructs
`elvProbeContentSpecialization D m Sc ν`, a unital k-algebra map from the existing **untruncated** `ELVOld.ContentRing D Sc (probeCutoff D m) ν` into the literal content-idempotent corner of the existing `heightAlgebra` at height ν.length.

The height quotient map is the identity on Hn at height zero and the existing cyclotomic quotient above zero. Vacuum descent uses the existing zero old ideal on the empty word. At positive height, the entry maps equal the previously constructed literal cyclotomic entries, and the target corner is the existing `CyclotomicContentCorner`. At the empty content its unit is the actual unit of Hn at height zero.

The finite matrix map preserves composition and identity. The sum of the source word identities is the literal target content idempotent. The inherited corner scalar action gives the canonical k-algebra structure. `elvProbeContentSpecialization_append_single` proves compatibility with existing `heightAppend` on every matrix generator, including the vacuum boundary.

Producer and closed mixed-parity rational consumers passed strict direct Lean checks, including the owner axiom audit of all 88 declarations. The fixtures check vacuum and positive content, the nonzero odd elementary value -3, and append compatibility. Full branch CI remains the integration gate.

This is the ring input for the probe-factor base change of InvertibleDotProbe.md Sections 1 and 5. It does not specialize a positive-weight truncated coefficient category. Existing `ContentCategory/contentAppend` in ELVContentModuleAction are based on `TruncatedCategory`; the probe action comparison must instead construct the untruncated category/module lift and preserve the categorical maps and prescribed inverses. The full module-action comparison is not proved by the ring map.
