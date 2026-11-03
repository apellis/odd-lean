# Inverses of the prescribed content E/F matrices

Brundan–Ellis (1.13)–(1.14), DeformedMatrixComparison (4), (5), require
inverses for the given matrices on the chosen content E/F composites.
`oldContentGridUnitMatrixComponent_bijective` and
`oldContentGridCapMatrixComponent_bijective` transport the established old
matrix inverses through the selected genuine finite chart squares. Their
sizes are exactly the unit/cap counts at content `i :: ν`, with the
corresponding nonnegative/nonpositive height hypotheses.

`oldContentGridUnitMatrixIso` and `oldContentGridCapMatrixIso` package
these bijections as isomorphisms of the chosen content modules. The `_hom`
equations identify their forward maps with the given
`gridUnitMatrixModuleMap` and `gridCapMatrixModuleMap`, retaining the
prescribed principal cup–crossing–cap, dotted unit/cap fields, and canonical
parity shifts. The `_inv_mem` theorems show the inverses are even. No
invertibility or chart-compatibility premise is added. The generic
`gridUnitMatrixModuleMap_mem` and `gridCapMatrixModuleMap_mem` expose the
evenness of the given assembled module maps before content specialization.

The module packaging is performed generically before substituting the
content data. It reconstructs the given homogeneous map from its
pointwise inverses, so naturality along every arrow in the output content
category follows from that map. Input-module naturality remains a separate
family-level assertion. No chart-evenness assumption is needed for the
pointwise transport: the given matrix itself is even.

The scope is full-coefficient untruncated content at explicit `i :: ν`.
The consumer uses both moving parities, positive and negative heights,
and both zero-height mate-only cases, proving every sign/count hypothesis.
Coefficient-truncated content, absent-i contents, original weights and the
normalized left inverse-row cap remain separate.
