# The untruncated old equal-colour braid

Brundan–Ellis Definition 1.5 requires the same-colour braid on three
successive inductions. `equalCrossComponent_braid` in `ELVOldAppendBraid.lean`, in
the `ELVOld.CyclotomicCrossingTensor` namespace, proves its coefficient
input on every object of the untruncated old category: append the chosen
equal crossing on the right to obtain the prefix crossing, and evaluate
the same chosen crossing at the appended object to obtain the suffix.
Their two three-crossing composites agree.

The argument descends the affine braid through `affineUnit` and the
literal old quotient. It retains every old word and full coefficients;
there is no power-annihilation condition or faithfulness assumption on
scalar specialization. The construction uses the positive physical
crossings. The prescribed negative induction crossing still needs its
three-induction flattening and whiskering comparison.

The producer and paired consumer pass strict checks with warnings as
errors and both compatibility settings. The consumer checks both moving parities,
empty and mixed old contexts, and the actual representable action on
every vector and an identity-plus-dot vector, and audits both owned
declarations against the axiom allowlist. The full build, global axiom audit and all non-vacuity checks passed in
[#1011](https://github.com/apellis/odd-lean/pull/1011), at source head
`77756d711f4e30fa50de52363f3a3d84e3075b81`
([CI run](https://github.com/apellis/odd-lean/actions/runs/41684396198)).

`ELVOldInductionBraid` supplies the subsequent direct-induction equation.
`oldTriplePrefixCross` and `oldTripleSuffixCross` are the independent
balanced transformations induced by those same two physical crossings.
`oldTripleCross_braid` proves their whole module-map braid on every input
old module. The superopposite signs introduced by contravariant induction
agree on the two paths; no evenness of the crossing is assumed.

This producer and its concrete consumer pass strict checking. The
consumer uses actual representables in empty and mixed contexts, both
moving parities, a parity-shifted module and the literal unit tensor, and
audits all 15 owned declarations. The full build, global axiom audit and all non-vacuity checks passed in
[#1011](https://github.com/apellis/odd-lean/pull/1011), at source head
`77756d711f4e30fa50de52363f3a3d84e3075b81`
([CI run](https://github.com/apellis/odd-lean/actions/runs/41684396198)).
[OldNestedBraid](OldNestedBraid.md) now supplies the comparison with
the prefix and suffix of the selected negative double-induction crossing
under the canonical flattenings, in strict paired checks. Restriction to
evaluated fixed contents and weight products remains separate.
