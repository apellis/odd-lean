# The selected tensor Hom is an exact-support object

`ELVContentHomVacuum.lean` places the already chosen
`WeightTensorVacuum.selectedHom` in the replete exact-content Hom category
of F4/(A1), with no supplied support or comparison premise.

`vacuumHom` is constructed on the exact empty probe and reservoir content
categories: forget the evaluated probe coefficient predicate and tensor
with the selected empty-word reservoir component. Its selected
whole-weight component is exactly the existing tensor-vacuum functor as
a Superfunctor (`selectedVacuum_component`), including all input maps.
At every other output content the selected reservoir word module is
zero by `PowerWordWeight.wordAt_isZero`. Tensoring that zero module with
the value of any input preserves zero. `selectedVacuum_off_isZero`
therefore covers every input and every colliding content block, rather
than inferring support from the regular-probe evaluation.

`selectedVacuum_supported` applies the checked selected-component/zero
criterion, and `supportedVacuum` has the literal existing selectedHom as
its underlying object. Together with `ELVContentHomClosure`, this gives
the two native missing-predecessor zero functors at the initial object
and preserves support under each present pre/post E/F operation and
parity shift. Every natural arrow between supported endpoints remains
available in the full subcategory.

The producer and paired consumer pass strict Lean 4.34.1 checks with
warnings as errors and both compatibility transparency settings false.
All 16 owned declarations pass the standard axiom audit. The consumer
uses a symmetric affine two-odd datum whose lowest-weight fibre contains
both zero and `[false,true]`. It tests actual selectedHom off-support
vanishing on every input, the whole native probe and reservoir boundary
zero functors, and a nonzero product of its two odd coefficients at the
regular input.

This identifies the initial supported object. The formal-sector action,
restriction of generator matrices and the central residual inversion
still require their own attachments. No assertion about support of all
whole-weight Hom objects is made.
