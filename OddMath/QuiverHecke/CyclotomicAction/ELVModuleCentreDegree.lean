import OddMath.QuiverHecke.CyclotomicAction.ELVModuleCentre

/-! # Integer degree of reconstructed content coefficients

Only source coefficients are graded here. The hypothesis tests the given
module-centre transformation on representables, retaining both parity pieces.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ModuleCentre
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I)

/-- The reconstructed source component is the total Yoneda evaluation of the
corresponding homogeneous module-centre component. No twist is discarded. -/
theorem reconstruct_app_evaluate (η : Centre D Sc cutoff N β) (p : ZMod 2)
    (v : ContentCategory D Sc cutoff N β) :
    (reconstruct D Sc cutoff N β η).app p v =
      ModuleYoneda.evaluate D Sc cutoff N β (contentRepresentable D Sc cutoff N β v)
        (η.app p (contentRepresentable D Sc cutoff N β v)) := by
  symm
  change (η.app p (contentRepresentable D Sc cutoff N β v)).total v (𝟙 v) =
    (η.app p (contentRepresentable D Sc cutoff N β v)).app p v (𝟙 v)
  exact congrArg (fun f => f (𝟙 v))
    (total_of_mem D Sc cutoff N β (η.app_mem p (contentRepresentable D Sc cutoff N β v)) v)

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- Exact criterion for source integer degree, tested on every representable
and both parity components of the given natural transformation. -/
theorem reconstruct_mem_degree_iff (η : Centre D Sc cutoff N β) (d : ℤ) :
    reconstruct D Sc cutoff N β η ∈ contentCoefficientDegree D Sc cutoff N β sy hc d ↔
      ∀ (v : ContentCategory D Sc cutoff N β) (p : ZMod 2),
        ModuleYoneda.evaluate D Sc cutoff N β (contentRepresentable D Sc cutoff N β v)
          (η.app p (contentRepresentable D Sc cutoff N β v)) ∈
            truncatedDegree D Sc cutoff sy hc N v.obj.word v.obj.word d := by
  constructor
  · intro h v p
    rw [← reconstruct_app_evaluate]
    exact h p v
  · intro h p v
    change (reconstruct D Sc cutoff N β η).app p v ∈
      truncatedDegree D Sc cutoff sy hc N v.obj.word v.obj.word d
    rw [reconstruct_app_evaluate]
    exact h v p

/-- Represented integer degree yields a source-central coefficient witness
whose action is the given transformation on every exact-content module. -/
theorem exists_coefficient_of_represented_degree (η : Centre D Sc cutoff N β) (d : ℤ)
    (h : ∀ (v : ContentCategory D Sc cutoff N β) (p : ZMod 2),
      ModuleYoneda.evaluate D Sc cutoff N β (contentRepresentable D Sc cutoff N β v)
        (η.app p (contentRepresentable D Sc cutoff N β v)) ∈
          truncatedDegree D Sc cutoff sy hc N v.obj.word v.obj.word d) :
    ∃ c : ContentCoefficient D Sc cutoff N β,
      c ∈ contentCoefficientDegree D Sc cutoff N β sy hc d ∧
        contentRealize D Sc cutoff N β c = η :=
  ⟨reconstruct D Sc cutoff N β η,
    (reconstruct_mem_degree_iff D Sc cutoff N β sy hc η d).mpr h,
    realize_reconstruct D Sc cutoff N β η⟩

end OddMath.QuiverHecke.ELVOld.ModuleCentre
