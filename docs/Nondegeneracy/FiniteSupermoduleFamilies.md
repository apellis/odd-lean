# Coordinatewise module-family comparisons

The finite shifted families in Brundan--Ellis (1.13)--(1.14) require the
chosen comparison at each coordinate to be natural in the input module.
`FiniteSupermoduleFamily.lean` supplies this product construction without
changing any coordinate map.

`productIso` retains the given component isomorphisms, and
`productIso_hom_mem` retains their evenness. `familyFunctor` acts by
`productMap` on both parity components. `familyNatIso` combines arbitrary
module-valued natural isomorphisms coordinatewise;
`familyNatIso_hom_total_apply` identifies its total component with the
given coordinate's total component.

The concrete consumer uses the selected preceding E/F comparison on a
mixed content module, after both canonical parity shifts. Its family
naturality is applied to the specified odd content induction dot and to
the inhomogeneous sum of identity and that dot. All declarations owned by
the producer, including generated declarations, pass the axiom audit.

This construction is the product comparison needed for transporting the
prescribed finite matrices. The chosen content unit/cap inverse natural
isomorphisms and their full entry identifications remain separate.
