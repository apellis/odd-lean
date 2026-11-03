# Finite matrix entries and the local inversion relations

`FiniteModuleLocalInverse` converts a specified even finite matrix isomorphism into the exact data structures `SKM.SuperSumInvFrom` and `SKM.SuperSumInvTo` used in BE (1.13)–(1.14). The coordinate set is `Option (Fin n)`: the principal coordinate is `none`, and the finite unit or cap slots are `some r`.

`localInverseFromColumns` and `localInverseToRows` retain the supplied forward principal field and every forward auxiliary field. The given isomorphism must have precisely the even matrix assembled from these fields and the given parity-restoring coordinate isomorphisms. The inverse entries are extracted by the finite module coordinate identities. `inverseUnitSlot` and `inverseCapSlot` extend the finite inverse entries by zero outside the window. All principal, orthogonality, finite-sum and parity identities are proved, with an arbitrary principal parity and auxiliary parity profile.

This is an intermediate matrix-to-relations construction. The selected weight-action application still needs a constructed finite matrix isomorphism and the comparisons identifying its forward fields with the prescribed mate and dotted cup or cap maps. It does not assert those isomorphisms from their desired inverse relations.

The paired concrete consumer uses truncated ELV representable modules with odd parity restoration. It checks both orientations, empty and nonempty windows, diagonal and off-diagonal identities, and the parity of entries outside the window. Producer and consumer pass scoped strict checking; all owned declarations pass the axiom audit. Full integration CI remains required.
