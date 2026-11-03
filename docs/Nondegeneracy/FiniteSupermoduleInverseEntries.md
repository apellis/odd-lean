# Finite matrix inverse entries for BE (1.13)–(1.14)

`FiniteSupermoduleInverseRows` and `FiniteSupermoduleInverseColumns` extract homogeneous inverse entries from a specified even finite matrix of modules. Each coordinate has a given parity-restoring isomorphism. The forward matrix is required to equal the matrix assembled from the specified forward fields; its inverse is projected or preceded by the canonical coordinate inclusion, then the coordinate parity is restored.

`forward_inverseCoordinateRow` and `inverseCoordinateColumn_forward` prove the diagonal identities. Their `_ne` counterparts prove orthogonality, and `sum_inverseCoordinateRow_forward` and `sum_forward_inverseCoordinateColumn` prove the total identities. The extracted entries have exactly the specified coordinate parity, including odd coordinates.

These are supporting results for the prescribed local inversion relations in BE (1.13)–(1.14). Their intermediate input is an isomorphism whose forward map is the specified finite matrix. Constructing that isomorphism for the selected weight action and identifying all its forward fields remain separate obligations. The paired concrete consumers use truncated ELV representable modules, odd parity restoration and all matrix identities. Both producer/consumer pairs pass scoped strict checking and owned-declaration axiom audits; full integration CI remains required.
