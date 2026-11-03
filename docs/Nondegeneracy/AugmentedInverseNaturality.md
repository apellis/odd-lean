# Input naturality of augmented inverse entries

`SuperSumInvFrom.ofSupernaturalComponents` and `SuperSumInvTo.ofSupernaturalComponents` bundle pointwise augmented inverse data into the full superfunctor category. Their only naturality inputs concern the specified forward principal and auxiliary fields. Naturality of the inverse entries is proved, including its Koszul sign against odd input morphisms.

The finite forward columns jointly detect outgoing maps, and the finite forward rows jointly detect incoming maps. `hom_ext` proves these statements directly from the augmented total identities. The principal and finite auxiliary inverse intertwining equations then follow by cancellation against all forward fields and their Kronecker identities. The principal and row/column `*_supernatural` theorems package these equations with the prescribed inverse parities. The base ring, principal parity and auxiliary parity profile are arbitrary.

An inverse auxiliary entry outside the finite window is unconstrained by `SuperSumInvTo` or `SuperSumInvFrom`. `zeroExtend` makes those entries zero before bundling. It preserves every forward field, the principal inverse, and every inverse entry inside the prescribed window. No claim of automatic naturality is made for arbitrary original entries outside that window.

These constructions supply the input-family step of BE (1.13)–(1.14) after the prescribed pointwise inverses have been constructed. They do not assume inverse naturality, a complete action family, flatness or new matrix isomorphisms.

Producer and paired concrete consumer pass scoped strict checking and all owned-declaration axiom audits. The consumer includes an even principal identity and odd parity-restoring principal and auxiliary inverses, empty and nonempty finite windows, actual odd input morphisms on superspaces, an explicitly nonzero finite inverse row on the one-dimensional superspace, and a nonzero original outside row changed to zero by extension. Full integration CI remains required.
