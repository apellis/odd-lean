# Relations on the supported Hom inputs

The central augmented inverse is proved for supported Hom objects. The
native presentation uses larger raw Hom categories, so this does not
give `CentralInvertible` or `LeftwardData.IsInverse` on every raw input.
The presentation nevertheless evaluates a local relation only on the
chosen rightmost input after applying a finite summand path.

`SupportedWhiskerReduction` makes this quantifier boundary explicit.
Let `Q t` be an object property in each raw Hom sector, preserved by
every native path functor, and suppose each chosen rightmost input
`Ys t` lies in `Q t`. If an unwhiskered relation vanishes on the
weight-matched objects in `Q`, its evaluation vanishes after every
valid left and right context. The proof uses the same finite path
decomposition as the raw reduction: its only use of the unwhiskered
equation is at `pathFunctor pv (Ys t)`, which lies in `Q` by the stated
closure condition.

`SupportedRelationLifting` defines `SupportedSectors.retainedInput` as the existing replete formal
content-support property, with the parameter-twisted OLD probe and ELV
reservoir. `retainedInput_path` discharges closure from the actual
supported path functor and `factor_path_obj`; it introduces no new
support-preservation premise. `relHolds_of_supported_compEval` then
produces precisely `RelHolds` for the native layer representation on
the included supported `Gs` and `Ys`. No change to the generator
images, context action or presented relations is made.

Both producers and their paired consumer pass scoped Lean 4.34.1
checks with warnings as errors and both compatibility settings. The
consumer retains both moving parities, arbitrary finite summand paths,
the actual supported rightmost families and arbitrary valid contexts.
The owned-declaration axiom audits cover both generic reduction
declarations and all ten supported attachment declarations, using only
the standard allowed axioms.
