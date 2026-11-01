# The suffix crossing as a natural family

The three-factor braid fields of Brundan–Ellis Definition 1.5 require the
second pair crossing as a supernatural transformation. Its data here are the
actual pair component on the first induced module:
`contentSuffixCrossMorphism` evaluates `contentEPairCrossTransform` on
`(contentE β i).obj M`. The first induction uses the existing named functor
and its structures. `contentSuffix_target_eq` fixes its pair target witness.

`contentSuffixCrossMorphism_source` identifies these module morphisms with
the canonical whiskered affine source. It follows from the existing component
comparison and total-evaluation detection. That equality proves naturality of
the independent family, giving `contentSuffixCrossMorphism_supernatural` and
`contentSuffixCrossTransform`. The total and double-total evaluation theorems
recover exactly the independent suffix component used in the braid paths.
No naturality or factor-action premise is supplied by the caller.

`BalancedInduction.supernatural_ext_total` records the detection step in a form
needed by the whole braid: parity projection of a total component recovers
its even or odd component. Consequently equality of every total component
implies equality of supernatural transformations, without a homogeneity
hypothesis. It applies both to module morphisms and to module-valued families.

The strict source and concrete connected asymmetric all-odd vacuum consumer
pass. The consumer covers unequal and equal suffix colours, includes the
parameter-twisted coefficients used by the action, and audits all nine owned
declarations. Full CI remains the integration gate. Whole braid equalities
and successor-block/weight-family transport remain downstream obligations.
