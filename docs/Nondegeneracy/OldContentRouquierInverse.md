# Old-content Rouquier inverse fields

The two producers `ELVInductionGridRouquierInverse` and
`ELVOldContentRouquierInverse` pass their strict source checks. They attach
constructed prescribed old-content matrix inverses to the actual ordinary
adjunction Rouquier mate and the specified dotted right-unit/right-counit
fields, using the local presentation's multiplicative parity profile.
No inverse naturality or matrix compatibility assumption is introduced.

Both producers and the mixed-parity consumer pass their strict scoped
checks. The consumer audits all 35 owned declarations against the three
standard Lean axioms and checks the finite identities in both height
directions using the constructed prescribed matrices. The adjacent one-letter Rouquier local
record still requires induction-composition transport of the literal old
two-strand relations. The checked empty-content local record is separate.
