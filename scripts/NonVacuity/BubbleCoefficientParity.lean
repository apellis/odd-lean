import OddMath.SKM.BubbleCoefficientParity

open CategoryTheory StringDiagrams Presentation
open OddMath.SKM
noncomputable section
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc) (μ : X)

example (i j : {i : I // D.parity i = 1}) :
    betaSYM cs μ (SYM.coefficientBasis D k (0, {i, j})) ∈
      closedPar D Sc μ (({i, j} : Finset {i : I // D.parity i = 1}).card : ZMod 2) :=
  beta_coefficientBasis_mem cs μ (0, {i, j})

example (q : ZMod 2) (p : SYM D k) :
    SYM.parityTwist D k q (SYM.parityTwist D k q p) = p := by simp

#print axioms OddMath.SKM.beta_coefficientBasis_mem
#print axioms OddMath.SKM.source_target_twist
#print axioms OddMath.SKM.SYM.parityTwist_comp
