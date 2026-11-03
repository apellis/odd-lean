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
declarations against the axiom allowlist. Full integration remains pending.
