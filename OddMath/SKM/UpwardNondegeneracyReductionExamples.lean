import OddMath.SKM.UpwardNondegeneracyReduction
import OddMath.SKM.SameColourSourceFrameExamples

/-! Concrete two-odd-colour consumption of the upward reduction.
The upward independence hypothesis is explicit: it is not proved here. -/
namespace OddMath.SKM.UpwardNondegeneracyReductionExamples
open SameColourSourceFrameExamples

/-- The reduction specializes to a concrete compatible two-odd-colour datum
and scalar system over the rationals. -/
theorem two_odd_colour_reduction (hUp : WeakMate.UpwardIndependence cs) :
    NondegeneracyConjecture cs := nondegeneracy_of_upward_independence cs hUp

/-- The exact remaining independence obligation for this concrete datum. -/
theorem two_odd_colour_iff :
    NondegeneracyConjecture cs ↔ WeakMate.UpwardIndependence cs :=
  nondegeneracy_iff_upward_independence cs

#print axioms two_odd_colour_reduction
#print axioms two_odd_colour_iff
end OddMath.SKM.UpwardNondegeneracyReductionExamples
