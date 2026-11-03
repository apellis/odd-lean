# Input-natural grid local inverses

Brundan–Ellis (1.13)–(1.14) needs inverse entries as supernatural
transformations, not merely separately selected maps on each input module.
`gridLocalInverseFromFamily` and `gridLocalInverseToFamily` apply the
augmented inverse naturality criterion to the specified grid mate and
ordinary dotted unit/cap fields. Their matrix isomorphisms remain explicit
intermediate inputs; the concrete old-content consumer supplies the
constructed prescribed matrix isomorphisms for every module, in both
moving parities and both height directions.

`gridMateTransformation`, `gridUnitColumnTransformation`, and
`gridCapRowTransformation` retain those exact forward fields. Their
`_total` equations expose the underlying module maps without any parity
coordinate convention being reintroduced after specialization. The inverse
entries retain the given finite window and are zero outside it, where the
augmented inverse identities otherwise impose no constraint.

This is a supporting implementation of the existing local-inverse route.
It does not assert a complete Rouquier family or change the normalized
left-counit convention. The native old probe construction still needs the
empty boundary and the dot/crossing/slide identifications of its local
Rouquier records.
