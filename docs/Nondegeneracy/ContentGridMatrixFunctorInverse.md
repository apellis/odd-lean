# Input-natural inverses of the chosen content E/F matrices

Brundan–Ellis (1.13)–(1.14) and DeformedMatrixComparison (4), (5) require
the prescribed matrices on the chosen content E/F composites to be
invertible naturally in the input module.
`oldContentGridUnitMatrixFunctorNatIso` and
`oldContentGridCapMatrixFunctorNatIso` prove this for the nonnegative and
nonpositive height cases, at their exact prescribed finite counts.

Their `_hom` equations identify the whole forward natural transformations
with the given `gridUnitMatrixInputNatTrans` and
`gridCapMatrixInputNatTrans`. The `_hom_app` equations retain the actual
module matrices and the explicit canonical finite-family endpoint
comparisons. The principal cup–crossing–cap and every dotted unit/cap
field remain unchanged. No inverse or chart-compatibility premise is
added: the component inverses are the proved chosen content module
isomorphisms of `ContentGridMatrixInverse.md`.

Naturality holds on all input-module maps, including odd and inhomogeneous
maps. Both directions have even module components by the `_even`
theorems. The source/target finite-family functors preserve addition,
scalar multiplication and both map parities, as established in
`InductionGridMatrixFunctor.md`. Thus these are even natural
isomorphisms of the chosen module-valued functors.

The strict source and concrete consumer cover both moving parities,
positive and negative heights, and both zero-height mate-only cases.
They test naturality of both inverse directions on the actual induced dot
and identity plus that dot, and audit every producer-owned declaration.
Full CI is the integration gate.

The scope is full-coefficient untruncated old content at explicit
`i :: ν`. Coefficient-truncated content, absent-i contents, original
weight transport and the normalized left inverse-row cap remain separate.
