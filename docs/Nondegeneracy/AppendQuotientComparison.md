# Comparing old and weighted-truncated append induction

`weightedRestrictionModuleIso` proves that restriction after descent
retains an annihilated old module. `quotientInducedWeightedModuleIso`
identifies quotient induction of that old module with its literal descent,
using the existing quotient-induction counit.

`oldAppend_truncate` proves that the actual old append functor commutes
with the actual further quotient on every old arrow. Therefore
`appendWeightedModuleIso` compares the descended old append induction
of a restricted truncated module with the existing truncated append
induction. It composes the preceding actual counit comparisons with
the proved `BalancedInduction.inductionComp` and this literal square.
No substitute induction, flatness, field or coefficient-evenness premise
is introduced.

Producer and concrete consumers passed pinned direct Lean with warnings
as errors and both compatibility settings. All 21 owned declarations
passed the consumer axiom audit. The consumer checks both inverse
products and applies the comparison to a provably nonzero induced vector
at every sufficiently large cutoff: the existing counit detects its unit
tensor as an odd-coefficient mixed crossing on a three-strand word.
Full CI remains the integration gate.

This is the append-induction quotient comparison needed by
SwappedVacuumCoordinates §6 and tracking #345. The result is a module
isomorphism for each input module. Naturality in that input, explicit
unit/counit and generator intertwining, and transport of the categorical
matrix to the exact-content/weight action remain separate statements.
No full action, bubble identity or nondegeneracy conclusion is supplied.
