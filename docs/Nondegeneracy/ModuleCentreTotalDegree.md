# Source coefficient degree from total represented evaluation

This is the reconstruction step for
[ReservoirClosureDegree](ReservoirClosureDegree.md). The module centre is
not assigned an integer grading on its arbitrary morphisms. Instead, its
action on each representable identity determines the degree of the
reconstructed source-central coefficient.

For a module-centre transformation `η` and a content-source object `w`,
`ModuleCentre.reconstruct_total_evaluate` identifies

```text
(reconstruct η).total w
  = (η.total (contentRepresentable w)).total w (𝟙 w).
```

The two outer parity components of `η` are homogeneous module maps.
Consequently their off-diagonal inner parity components vanish. The two
remaining diagonal terms are precisely the two source components used by
`reconstruct`.

`reconstruct_app_eq_proj_total` recovers each source parity component as
the parity projection of this total coefficient. The independent integer
grading on the content source is preserved by those projections. Hence
`reconstruct_mem_degree_of_total_evaluation` proves that `reconstruct η`
belongs to `contentCoefficientDegree d` whenever the displayed total
evaluation belongs to `truncatedDegree d` for every `w`.

This criterion reduces the final chosen-closure attachment to its total
represented action. It requires no separate homogeneous-parity premise
and no comparison supplied by the caller. The paired consumer instantiates
the criterion on a positive-content odd representable whose identity and
odd exterior vector are independently nonzero, and audits every owned
declaration against the repository axiom allowlist.

The producer and paired consumer pass strict scoped checking with Lean 4.34.1,
warnings as errors and both prescribed transparency compatibility options.
All three owned declarations pass the standard axiom allowlist audit.
Full package CI remains the integration gate.
