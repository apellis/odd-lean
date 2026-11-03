# Local inverse columns of the given weighted cap matrix

`weightedContentLocalInverseTo` constructs `SKM.SuperSumInvTo` for the specified weighted matrix mate and ordinary dot/cap rows restricted to one output content. It uses the proved `weightedContentCapMatrixIso` and its exact given forward map, with only the cap-branch height inequality. The finite count is `contentCapCount`, and the principal and auxiliary degrees remain `D.parity i` and `n • D.parity i`.

`restriction_finiteRows` retains the literal rows and the canonical finite product coordinate under restriction. The inverse columns are then extracted using the restricted chosen parity-restoring isomorphisms. No inverse or compatibility hypothesis is added.

The input is a global truncated-category module. The output is local inversion data on its restriction to the specified output content. Transport to arbitrary canonical content inputs and to the selected weight action requires the corresponding chosen source, target and value chart squares; it is not asserted by this construction alone.

Producer and paired concrete consumer pass scoped strict checking and all owned-declaration axiom audits. The consumers use both moving parities, shifted truncated representables, the prescribed nonempty cap window and the zero-height empty window, including the total, principal, orthogonality and parity identities. Full integration CI remains required.
