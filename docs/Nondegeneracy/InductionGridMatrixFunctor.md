# Input-module functors of the prescribed finite matrices

DeformedMatrixComparison (4), (5) requires the whole matrices to be
natural in arbitrary input-module maps. `gridUnitMatrixSourceFunctor` and
`gridCapMatrixTargetFunctor` assemble their canonical shifted families.
They preserve addition, scalar multiplication and both morphism parities.

`gridUnitMatrixInputNatTrans` and `gridCapMatrixInputNatTrans` assemble the
prescribed entry natural transformations by finite columns and rows.
Their `_app` equations identify the components with the same
`gridUnitMatrixModuleMap` and `gridCapMatrixModuleMap`, retaining the
explicit finite-family object equality. The `_app_mem` theorems show each
component is even. Naturality covers odd and inhomogeneous input maps.

`gridUnitMatrixInputComponentIso` and `gridCapMatrixInputComponentIso`
transport a component isomorphism to the literal input-functor endpoint.
Their `_hom` equations recover the natural-transformation component
whenever the supplied component has the prescribed forward map. These
are endpoint adapters for the already proved chosen content inverses of
`ContentGridMatrixInverse.md`, not assumptions of matrix invertibility.

The strict source and concrete consumer range over both moving parities
and all finite sizes, including zero. They test the actual induced dot
and identity plus that dot as input maps, and apply both endpoint adapters
to the prescribed chosen content module inverses. Every producer-owned
declaration is audited. Chosen content input-natural isomorphisms are the
next specialization; this generic module adds no coefficient or weight
transport claim.
