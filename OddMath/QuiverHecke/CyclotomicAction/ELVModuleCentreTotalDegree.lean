import OddMath.QuiverHecke.CyclotomicAction.ELVModuleCentre

/-! # Total representable evaluation and source coefficient degree

The reconstruction step in ReservoirClosureDegree can be checked on the
total action at each representable identity. Independent parity projections
then recover both components without grading arbitrary module morphisms.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
namespace OddMath.QuiverHecke.ELVOld.ModuleCentre
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I)

/-- Total source reconstruction is the total module action on its represented
identity. Both off-diagonal parity components vanish by homogeneity. -/
theorem reconstruct_total_evaluate (η : Centre D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N β) :
    (reconstruct D Sc cutoff N β η).total w =
      (η.total (contentRepresentable D Sc cutoff N β w)).total w (𝟙 w) := by
  let R := contentRepresentable D Sc cutoff N β w
  change (η.app 0 R).app 0 w (𝟙 w) + (η.app 1 R).app 1 w (𝟙 w) =
    (((η.app 0 R).app 0 w + (η.app 1 R).app 0 w) +
      ((η.app 0 R).app 1 w + (η.app 1 R).app 1 w)) (𝟙 w)
  rw [Superfunctor.app_eq_zero_of_mem (η.app_mem 1 R) (q := 0) (by decide),
    Superfunctor.app_eq_zero_of_mem (η.app_mem 0 R) (q := 1) (by decide)]
  simp only [add_zero, zero_add, SVec.add_apply]

/-- The parity component of the reconstructed coefficient is its ordinary
source parity projection, independently of integer degree. -/
theorem reconstruct_app_eq_proj_total (η : Centre D Sc cutoff N β) (p : ZMod 2)
    (w : ContentCategory D Sc cutoff N β) :
    (reconstruct D Sc cutoff N β η).app p w =
      proj k p ((reconstruct D Sc cutoff N β η).total w) := by
  symm
  rcases parity_eq_zero_or_one p with rfl | rfl
  · exact proj_eq_of_add rfl
      ((reconstruct D Sc cutoff N β η).app_mem 0 w)
      ((reconstruct D Sc cutoff N β η).app_mem 1 w)
  · exact proj_eq_of_add (add_comm _ _)
      ((reconstruct D Sc cutoff N β η).app_mem 1 w)
      (by simpa using (reconstruct D Sc cutoff N β η).app_mem 0 w)

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- Source integer degree follows from the total action on every represented
identity; both parity projections preserve that same integer degree. -/
theorem reconstruct_mem_degree_of_total_evaluation (η : Centre D Sc cutoff N β) (d : ℤ)
    (h : ∀ w : ContentCategory D Sc cutoff N β,
      (η.total (contentRepresentable D Sc cutoff N β w)).total w (𝟙 w) ∈
        truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word d) :
    reconstruct D Sc cutoff N β η ∈ contentCoefficientDegree D Sc cutoff N β sy hc d := by
  intro p w
  change (reconstruct D Sc cutoff N β η).app p w ∈
    truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word d
  rw [reconstruct_app_eq_proj_total, reconstruct_total_evaluate]
  exact (contentGradedSupercategory D Sc cutoff N sy hc β).proj_mem_degree p (h w)

end OddMath.QuiverHecke.ELVOld.ModuleCentre
