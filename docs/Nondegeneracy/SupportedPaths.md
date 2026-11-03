# Supported path inclusion

`SwappedAssembly/SupportedPaths.lean` supplies the path charts needed to
restrict the native generator matrices to F4/(A1). `nativePathFunctor`
composes the prescribed native OLD/ELV steps along an actual `SPath`;
`pathFunctor` composes their canonical full-subcategory restrictions.
Formal endpoints and each step's parity-shift placement are retained.

`pathFunctor_inclusion` identifies the whole included supported word
functor with the native word functor. Its induction uses the checked
`step_inclusion`, with no chosen word isomorphism or assumed comparison.
The equality includes objects and all homogeneous maps. It is the
computed path transport for the next attachment to `ProbeReservoir.GenImage`.

The producer and occupied consumer pass strict Lean 4.34.1 checks with
warnings as errors and both compatibility transparency settings false.
All 10 owned declarations pass the standard axiom audit. The consumer
uses an actual supported tensor Hom with a nonzero product of two odd
coefficients in an affine collision fibre. It tests the empty path, the
probe EF cap path, the reservoir FE cup path, and a mixed word whose outer
reservoir step has nonempty odd probe content and a nontrivial parity
shift. Every path-validity and endpoint condition is proved.

Attachment to the complete chosen factor record, restriction of its
literal generator entries and the full supported presentation remain
separate. This result does not assert the missing central inverse.
