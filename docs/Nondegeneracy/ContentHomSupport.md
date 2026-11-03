# Exact-content Hom support and formal boundaries

The approved F4 and (A1) of `SwappedActionAssembly.md` prescribe
`SFun(T_b,W_c)` at each pair of formal nonnegative contents, with zero
categories at absent contents. This differs from the unrestricted
`ProbeReservoir.H` in `SwappedAssembly/Sectors.lean`: that category is the
whole Hom between factor categories at the two original weights.

The distinction matters when formal contents have the same root image.
`CyclotomicAction.Global.WeightBlocks` retains every such content.
`exists_blockSucc_iff` identifies absence of a native predecessor with
absence of the moving colour from the **evaluated content block**. It
does not identify it with absence from another formal content at the same
weight. The checked `ELVWeightMatrixHeight` consumer has the empty content
and `[false,true]` at the same lowest weight for the symmetric affine
two-odd Cartan matrix. Both colours have a predecessor in the latter
block. The `ELVPowerWordWeight` collision consumer also retains a present
predecessor outside the support of its selected word module.

Consequently a formal condition `b_i=0` or `c_i=0` cannot alone remove the
corresponding native composite on an arbitrary object of whole-weight
Hom. The optional path-index matrix charts and the entry comparisons on
present paths remain valid. Attaching full native factor inverses at
absent corners additionally requires exact-content support. No claim
that every whole-weight Hom object has this support is made.

The existing pairing extension adjoins independent coroot coordinates,
but its roots are `(alpha_i,0)`. It preserves every original root-content
collision. It supplies the balanced dominant weights, rather than a
solution to this support issue. No extra root-independence premise is
introduced.

The exact-content route realizes an arbitrary superfunctor
`G:T_b -> W_c` inside the original-weight products by input projection at
b and output zero extension at c. This keeps all original-weight blocks,
with genuine zero modules at the other outputs. On all objects and maps,
the selected output is exactly `G(M_b)` and `G(f_b)`. The category of G's
is the literal category required by (A1); it is not an assertion that the
embedding exhausts whole-weight Hom.

At a probe boundary, precomposition by induction has zero selected
b-component when b lacks the moving colour. Additivity of G then kills
its whole realization. At a reservoir boundary, restriction of a family
supported at c is zero when c lacks that colour. These arguments retain
collision blocks. On present edges, the four primitive operations are
composition with the corresponding chosen block induction or restriction;
parity shifts preserve the zero components. These are the primitive
support comparisons needed to assemble the action on (A1).

`WeightTensorVacuum.selectedHom` is aligned with this construction: its
input is the projection `emptyProbe`, and its reservoir family is
`ReservoirWordValue.initialValue`, the empty-word `wordFamily`.
`PowerWordWeight.wordAt_isZero` gives its zero components away from formal
content zero. The initial selected Hom therefore has exact support
(0,0); evaluation of it at the regular probe alone would not suffice to
prove this all-input support claim.

`ELVContentHomSupport.lean` implements the exact-content category and its
whole-weight realization. `component_selected`, `obj_selected` and
`map_selected` retain the projection formula; `obj_off_isZero` and
`obj_isZero_of_input` retain all output-zero components. The four
`preE_component`, `preF_component`, `postE_component` and `postF_component`
equalities identify the selected primitive **Superfunctors**, on all maps.
`postE_off_isZero`, `postF_off_isZero`, `preE_absent_isZero` and
`postF_absent_isZero` give the primitive support/absent component results;
`shift_component` and `shift_off_isZero` handle parity shifts.

The producer and concrete collision consumer pass strict Lean 4.34.1
checks with warnings as errors and both compatibility transparency
settings false. All 35 owned declarations pass the standard axiom audit.
The consumer uses actual OLD probe and regular-power reservoir module
categories, proves a nonzero two-odd coefficient in the realized functor
at its regular input, identifies its selected component with
`selectedHom` on every input, and tests all four primitive operations and
both absent cases in the colliding weight fibre.

The replete supported full subcategory and whole even natural-isomorphism
closure, the full action and its inverse matrices remain separate
attachments. No whole-Hom central invertibility or uniform whole-weight
nilpotence conclusion is included.
