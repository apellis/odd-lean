# Inverses of the prescribed weighted matrix components

DeformedMatrixComparison (2), (4) requires the actual weighted unit and cap
forward matrices, in their prescribed parity coordinates, to be invertible.

`weightedUnitMatrixComponent_bijective` and
`weightedCapMatrixComponent_bijective` follow from the complete chosen
chart squares and the actual old `moduleUnitMatrixIso` /
`moduleCapMatrixIso`, under the exact content height sign hypotheses.
There is no supplied matrix compatibility or invertibility hypothesis.

`weightedUnitMatrixComponentIso` and `weightedCapMatrixComponentIso` have
literally `weightedUnitMatrixComponent` and `weightedCapMatrixComponent`
as their forward maps, as proved by the `*_hom` equations. The four
`*_hom_inv_id` / `*_inv_hom_id` equations explicitly use those given forward
maps. Both forwards and inverses have degree zero. Arrow objects retain
the existing domain and codomain of each given map; they change neither
its parity structure nor its entries.

The producer and paired consumer pass the pinned strict checks, auditing
all 33 owned declarations. The tests include both moving parities, the
connected asymmetric datum, positive unit counts 8 and 10, negative cap
count 1, the height-zero mate-only cases and the vacuum.

These are component isomorphisms on arbitrary truncated supermodules at
the specified word. Module-functor assembly and the global categorical
action remain separate steps; the whole nondegeneracy proof is not claimed
here.
