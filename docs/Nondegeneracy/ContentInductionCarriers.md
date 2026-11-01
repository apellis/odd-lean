# Content induction carrier compatibility

DeformedActionAssembly.md §5 compares successive single-letter induction with
block induction. The comparison equivalences and independent dot components
must retain the module structures of the evaluated induction functors.

`ContentEPairSpace` and `ContentETripleSpace` take the carrier of the evaluated
pair and triple SVec objects. The block codomains of `contentEPairEquiv` and
`contentETripleEquiv` likewise use the evaluated block SVec objects. The
functors and comparison isomorphisms are unchanged.

`contentAppendTo` retains its explicit common target and its previous object
and map formulas. It is defined in `ELVContentModuleAction`, and
`contentAppend` is its canonical-target specialization. The explicit-target
additive, linear and superfunctor instances remain in
`ELVContentModuleTransform`.

The pair inner dot evaluates induction on the existing first-dot component;
the outer dot evaluates the existing last-letter component at its recast
content. `contentInductionMap_total_of_mem` and
`contentInductionTransform_total` identify these natural-map evaluations with
the balanced raw formulas. The public whiskering equalities use the natural-map
evaluations. The pair dot comparisons and ordered quadratic retain their
statements. The triple last dot uses the same component evaluation, and the
three positioned-dot comparisons retain their statements.

Composition of source comparison squares uses a generic equality before
specializing to content modules. Negation of a transported triple map likewise
uses linear-map composition before specialization. No extra action, inverse,
independence or grading hypothesis is introduced. The independent composed
braid and distinct-slide relations remain separate obligations.
