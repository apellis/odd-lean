# Even induction maps and unit generators

Current scope and verification are maintained in [STATUS](STATUS.md). Any original
topic-head pending checks below are historical; they do not override the consolidated
status or establish completion of the full conjecture.

`ELVInductionUnitNaturality` proposes `BalancedInduction.moduleMorphism_total_tensor_even`: for any even module morphism f from balanced induction to an arbitrary target module H, f([g⊗b]) equals H(g) applied to f(unit(b)). The arrow g is fully inhomogeneous. The statement assumes no unit-compatibility conclusion; it is the ordinary naturality of an even module map evaluated on the unit, followed by `postcompose_unit`.

The producer and paired actual old-append/representable-counit consumers are unverified drafts. No new checked comparison claim is asserted.

For the weighted comparison, name the literal old module morphism f = weightedRestrictionModuleIso(...).inv followed by restriction of the chosen appendWeightedModuleIso.hom. Its evenness follows from the separate weighted parity results. Its total getter is the chosen comparison on unchanged old vectors, because the first isomorphism has identity components. The generic tensor formula and the chosen comparison's unit formula then give the full weighted tensor formula without reducing arbitrary weighted action records. The scalar comparison uses the analogous proved restriction/descent identity. Crossing and adjunction transport remain further obligations.
