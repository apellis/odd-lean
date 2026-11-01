# Actual ordinary probe modules on the untruncated old content category

`ELVOldContentCategory.lean` restricts the existing full old ELV category to
a finite permutation class of words. It inherits the existing quotient Homs,
super grading and linear structure. Its right append is the already
established canonical old append functor, restricted to those contents.
The target content frame is `i :: ν`, so its height is definitionally
`ν.length + 1` and includes the vacuum step.

`ELVProbeOldModule.lean` constructs `probeOldModule D m Sc ν M` as a
genuine additive linear superfunctor to SVec. For a module over the prescribed
ordinary probe height algebra, its value at a word is the actual fixed
subspace `e_word M`. An old morphism acts by left multiplication by its
checked scalar-specialized rectangular entry. The identity, composition and
super parity laws are proved, without an assumed module-action comparison.
An arbitrary existing right grading is retained, so this includes both
HeightModules (trivial right grading) and canonical regular bimodules.

Strict local checks pass for both producers and all paired consumers.
The old-content owner audit checks 73 declarations and the probe-module
owner audit checks 36. Closed consumers include mixed odd/even content and
a rational vacuum regular-module vector proved nonzero using the existing
nonzero vacuum inclusion. They check actual identity, scalar and parity
actions. Full CI is the integration gate.

This constructs the old module itself. Its comparison with ordinary probe
induction, categorical adjunctions and prescribed inverse matrices remains
separate. The source is untruncated; no binomial evaluation is applied to a
positive-weight coefficient truncation.
