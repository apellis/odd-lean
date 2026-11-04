# Chosen factor paths and supported generator entries

`SupportedFactorPaths.lean` attaches the complete chosen
`elvProbeReservoir` factor record to the supported-sector construction of
SwappedActionAssembly F4/(A1)–(A3). The ambient coefficient presentation is
`parameterTwist D Sc`, as in the chosen factor constructor.

`factor_step` identifies all four factor steps with `nativeStep`. The
identities preserve the output shift on pre-F and post-E and the input
shift on post-F. `factor_pathFunctor` identifies their whole path
functors. `factor_pathFunctor_inclusion` then gives the actual chosen
factor path after the canonical full inclusion of the supported sector.
These comparisons require no new support-preservation, word-isomorphism
or faithfulness hypothesis.

`SupportedGeneratorEntries.lean` keeps the same `SPath` indices and
formal endpoints in `GeneratorEntry`. `restrictGenImage` restricts any
existing `P.GenImage`. Its included components are the literal factor
components in the computed path charts (`restrictGenImage_hom`).
`restrictGenImage_mem` preserves parity, and
`restrictGenImage_supernatural` preserves the signed naturality equation.
`generatorTransformation` packages these entries as transformations
between the existing supported path functors; its designated component
and parity are checked by `generatorTransformation_app` and
`generatorTransformation_mem`.

`upwardImage` attaches the existing `P.upwardGens` matrices. Its
supernaturality theorem retains the intermediate hypothesis
`CrossCoeff.IsSupernatural`; no central inverse, complete supported
presentation or nondegeneracy conclusion follows from this attachment.
Dot, rightward cup and rightward cap already have the required native
supernaturality proofs independently of that mixed coefficient input.
The actual coefficient's supernaturality follows separately from its
constructed denominator units and inverse identities; the paired
consumer uses that theorem to instantiate the supported equal-colour
mixed crossing.

The paired consumer uses the symmetric affine two-odd collision datum.
The selected exact-support tensor Hom is occupied by the nonzero product
of the two independent odd coefficients at the regular probe input.
It constructs supported dot, cap and cup matrix entries, the odd dot
transformation, and the mixed equal-colour crossing with the constructed
inverse coefficient. All coefficient-naturality and cutoff inputs are
proved. A dot entry at nonempty odd probe content also exercises the
nonzero post-E content shift. It audits both producers against the
standard axiom allowlist.
