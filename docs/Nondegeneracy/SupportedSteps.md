# Native steps on supported formal sectors

`SwappedAssembly/SupportedSteps.lean` gives the four primitive functors
of F4/(A1)–(A3) on the supported formal sector categories. `nativeStep`
is constructed from the actual global OLD probe and full-ELV reservoir
E/F functors, with the existing original-weight edge certificates.

The shift conventions agree with the prescribed Hom construction:

- pre-E has no parity shift;
- pre-F has the output shift `leftAdjParity` at its probe-down edge;
- post-E has the output shift `homContentShift` at the sector's formal
  probe content;
- post-F has that content shift on its input, before restriction.

The ambient Hom parity completion is `homPiLeft`. `nativeStep_closed`
uses the computed block-successor equations, the checked replete
primitive closure and parity-shift closure. It retains every object of
the supported category and all original-weight collision blocks.
`step` is its canonical full-subcategory restriction, and
`step_inclusion` identifies the entire included functor with the literal
native step on objects and maps. There is no supplied functor-comparison
or faithfulness premise.

The paired consumer starts with the actual occupied tensor Hom on a
symmetric affine two-odd collision datum, and constructs the required
supported objects by these steps with their genuine formal return
transports. It exercises all four functors and inclusion identities.
A nonempty odd probe content also gives a nonzero reservoir content
shift, so the shifted post-E case is explicitly instantiated. The
independent product of the two odd coefficients survives in the initial
regular input.

The actual complete ProbeReservoir factor record must still be attached
to these native E/F fields, followed by restriction of its generator
matrices and verified presentation relations. This module alone does not
assemble the full supported action or prove central invertibility.

The producer and paired consumer pass strict Lean 4.34.1 checks with
warnings as errors and both compatibility transparency settings false.
All 19 owned declarations pass the standard axiom audit.
