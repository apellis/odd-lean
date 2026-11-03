# Distinct mates on the evaluated OLD probe

Brundan–Ellis Definition 1.5, (1.12), requires the inverse of the actual
positive distinct cup-crossing-cap. `ELVContentDistinctIso.lean` already
constructs `oldContentDistinctMateModuleIso` on untruncated OLD content
modules, and `oldContentDistinctMateFunctorIso` makes this inverse natural
on arbitrary input maps. These results do not require a local inversion
or factor-action premise.

`ELVProbeEvaluatedDistinctMate.lean` restricts the same forward and inverse
through the full scalar-evaluated subcategories. Its source is lower
j-restriction followed by lower i-induction; its target is upper
i-induction followed by upper j-restriction, with the latter append stored
at `i :: j :: ν` using its prescribed swap certificate. Induction and
restriction closure put both endpoints in the evaluated category, which
retains every even and odd module map, so the OLD inverse remains a map
of that category without an extra preservation hypothesis.

`probeEvaluatedDistinctMateComponent` retains the whole OLD forward.
`probeEvaluatedDistinctMate` uses `fullLiftTrans` to inherit the input-map
law, and its source and target functors equal the chosen evaluated E/F
composites. `probeEvaluatedDistinctMateModuleIso_inv_native` identifies the literal
inverse. `probeEvaluatedDistinctMateIso` gives both whole-functor inverse
identities, with inverse degree p(i)p(j). The paired consumer includes
connected mixed and two-odd-colour data, actual regular probe modules,
both round trips and naturality on an odd parity-isomorphism input.

The producer and paired consumer pass strict scoped checks with warnings
as errors and both compatibility settings. The consumer audits all 54
owned declarations against the standard axiom allowlist. Full integration
verification remains separate.
This constructs the chosen evaluated mate at stored contents; its
identification with the complete probe Rouquier presentation still needs
the independently chosen crossing/right-adjunction square and canonical
content and weight transport. No probe braid field is claimed here.

The source head `4da876539f5147f00b608e0f0abf9f53f5808a92` passed the
full build, global axiom audit and every non-vacuity consumer in
[#1013](https://github.com/apellis/odd-lean/pull/1013)
([CI run](https://github.com/apellis/odd-lean/actions/runs/41687376775)),
merged at `73318d56`.
