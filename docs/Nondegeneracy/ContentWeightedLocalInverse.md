# Local inverse rows of the given weighted matrix on one output content

`weightedContentLocalInverseFrom` constructs `SKM.SuperSumInvFrom` for the specified weighted matrix mate and ordinary unit/dot columns restricted to a fixed output content. Its only sign condition is the unit branch height inequality. The finite count is the prescribed `contentUnitCount`; the principal parity and auxiliary profile remain `D.parity i` and `n • D.parity i`.

The construction uses the already proved `weightedContentUnitMatrixIso`, with its exact given forward map. Restriction retains the literal finite module product and all its columns, as proved by `restriction_finiteProduct` and `restriction_finiteColumns`. The canonical parity coordinates are restricted unchanged before extracting the inverse entries. No inverse or compatibility hypothesis is added.

The input is a module on the global truncated category. The output is local inversion data on its restriction to the selected content. This includes contents lacking the moving colour: no lower append functor is required. Transport from an arbitrary canonical content input through its extension unit and the selected upper append chart remains a separate obligation, as does the final selected weight-action local inversion.

Producer and paired concrete consumer pass scoped strict checking and all owned-declaration axiom audits. The examples use both moving parities, shifted truncated representables and empty or nonempty absent-colour output content. They check the total, principal, orthogonality and parity identities. Full integration CI remains required.
