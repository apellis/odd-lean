import OddMath.SKM.SameColourSourceDescent
import OddMath.SKM.SameColourTargetDescent
import OddMath.SKM.WeakMateIndependence

/-!
# Reduction of nondegeneracy to upward independence

Contextual source and target descent reduce arbitrary oriented boundaries to
sorted ones. Literal inverse mates then reduce sorted boundaries to upward
boundaries, allowing the external weight to change. The only independence
hypothesis below is upward independence at every weight over the full abstract
coefficient algebra `SYM`.
-/
noncomputable section
namespace OddMath.SKM
open StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- Upward independence at every weight implies the full nondegeneracy
conjecture, for every oriented boundary and every complete decorated choice.
No field, finite-colour, grading or coefficient-homogeneity premise is needed. -/
theorem nondegeneracy_of_upward_independence (cs : CScalars Sc)
    (hUp : WeakMate.UpwardIndependence cs) : NondegeneracyConjecture cs := by
  apply nondegeneracy_of_contextual_descent cs ?_
    (source_exchange_descent cs) (target_exchange_descent cs)
  intro μ l r a b _ F
  exact WeakMate.sorted_independence cs hUp l a b r μ F

/-- Full nondegeneracy is equivalent to its upward part at every weight. -/
theorem nondegeneracy_iff_upward_independence (cs : CScalars Sc) :
    NondegeneracyConjecture cs ↔ WeakMate.UpwardIndependence cs := by
  constructor
  · intro h a b hab μ U
    exact (nondegeneracyConjecture_iff_injective cs).mp h (ups a) (ups b) hab μ U
  · exact nondegeneracy_of_upward_independence cs

#print axioms nondegeneracy_of_upward_independence
#print axioms nondegeneracy_iff_upward_independence
end OddMath.SKM
