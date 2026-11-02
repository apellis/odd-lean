# Scalar comparison of the ordinary counit

**Scoped-checked; full CI pending.** The producer and its paired connected,
mixed-parity consumer pass the pinned strict checks. All 40 owned declarations
pass the axiom allowlist.

`probeAppendOrdinaryCounitLinear` uses four prescribed legs: the selected append comparison,
induction of `probeOrdinaryRestrictionModule_eq`, the literal ordinary counit,
and the existing scalar-restriction equality isomorphism back to the old module
values. The last coordinate map is identity on vectors; it exposes the source
and target supervector spaces explicitly rather than relying on implicit
retargeting of a linear map.

On an old generator `[g ⊗ b]`, the calculation sends it first to
`[U.map g ⊗ b]`, keeps its vector under the restriction equality, evaluates the
ordinary counit to `O.map (U.map g) b`, and then uses scalar quotient action to
obtain `N.map g b`. `probeAppendOrdinaryCounitLinear_eq` identifies the whole
composite with the literal old counit on every output word and every coend
vector. The input
module retains the documented scalar coefficient evaluation hypothesis;
no faithfulness, dimension or homogeneous-generator premise is introduced.

The proof computes the transpose on raw coends with an independent input
supermodule before specializing it to the restriction of the target module.
The identity input map then recovers the canonical counit. This keeps the
chosen module coordinates throughout the operator comparison.

The companion consumer uses connected mixed-parity regular probe modules,
with both moving parities and vacuum source content. This result compares
the ordinary unshifted adjunction counit. Normalized caps, crossings,
inverse matrices and full factor assembly remain separate.
