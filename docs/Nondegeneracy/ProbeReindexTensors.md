# Balanced tensors under OLD representative changes

The representative comparison in `ELVProbeReindexInduction` is the
unique comparison between the specified balanced append left adjoints of
the same literal restriction functor. Its tensor formula is needed to
transport the chosen dot and crossing, and hence the inverse matrices in
Brundan–Ellis (1.12)–(1.14), to canonical multiset representatives.

Write `Q : Cν → Cμ` and `Q' : Cν' → Cμ'` for the certificate changes,
and `J : Cν → Cν'`, `K : Cμ → Cμ'` for append. The square
`J ⋙ Q' = Q ⋙ K` is literal. Pullback along the inverse certificate
changes gives the corresponding module reindex functors. Their strict
equivalence adjunctions have identity unit and counit. Therefore the unit
of append followed by output reindexing is the original append unit,
while the unit of input reindexing followed by append is the reindexed
append unit. The adjunction-uniqueness comparison identifies these units.

Every balanced tensor `[g ⊗ b]` is the postcomposition of `[id ⊗ b]`
by `g`. Even naturality of the comparison then gives
`[g ⊗ b]` at the old source object `s` mapping to `[g ⊗ b]` at `Q(s)`.
The arrow and coefficient vector are unchanged: only permutation
certificates change. This argument applies to arbitrary arrows and
vectors, including inhomogeneous ones.

The declarations in `ELVProbeReindexTensors` implement this unit and
tensor calculation. Generator and local inverse-record transport are
subsequent obligations; neither follows merely from the existence of an
unspecified induction isomorphism.

`oldAppendReindexLeftAdjunction_unit` and
`oldAppendReindexRightAdjunction_unit` identify the two composite units.
`oldAppendReindexIso_hom_unit` gives their equality on every coefficient
vector. `oldAppendReindexLinear` fixes both coend carriers before applying
the canonical comparison, and `oldAppendReindexIso_hom_tensor` gives its
tensor formula. `probeAppendReindexIso_hom_linear` identifies this map
with the comparison in the full evaluated probe categories.

The producer and paired consumer pass strict scoped checks with warnings
as errors and both compatibility settings. The consumer uses connected
even/odd data, regular probe modules, a nontrivial base permutation and a
canonical upper representative. It applies the unit and tensor formulas
to arbitrary vectors and arrows, retains odd-input naturality, and audits
all 27 owned declarations against the permitted axioms. Full integration
verification remains separate. The existing comparison isomorphism
supplies its chosen inverse; a separate inverse tensor formula is not
needed for transport by this isomorphism.
