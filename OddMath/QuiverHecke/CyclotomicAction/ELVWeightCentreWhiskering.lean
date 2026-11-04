import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCentreBlocks
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ReservoirCoefficients

/-! # Exact-content evaluation of coefficient actions

SwappedHomInversion §4, condition (J): evaluating the post-whiskering
coefficient action at an output content gives the action of the restricted
coefficient. This identifies the whole-weight closure action with the
content coefficient ideal without a uniform bound on the weight fibre.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightCentreBlocks
open CyclotomicAction SwappedAssembly
universe u
private theorem postCoeff_eq_whiskerLeft {k : Type u} [CommRing k]
    {A B : PiSCat.{u,u,u + 1} k} (Z : A ⟶ B) (η : End (𝟙 B)) :
    ProbeWindow.postCoeff Z η = Superfunctor.whiskerLeft Z η := by
  unfold ProbeWindow.postCoeff
  simp only [PiSCat.rightUnitor_inv, PiSCat.rightUnitor_hom]
  erw [Category.id_comp, Category.comp_id]
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) {x : X} (β : WeightBlocks D Λ x) (T : PiSCat.{u,u,u + 1} k)

/-- Output projection preserves the action of a whole-weight central coefficient. -/
theorem postCoeff_evaluate (Z : T ⟶ elvWeightSpace D Sc cutoff N Λ x)
    (η : End (Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x))) :
    Superfunctor.whiskerRight (ProbeWindow.postCoeff Z η)
      (elvBlockEval D Sc cutoff N Λ β) =
        ProbeWindow.postCoeff (B := PiSCat.{u,u,u + 1} k)
          (a := T) (b := contentModuleTarget D Sc cutoff N β.1)
          (Z.comp (elvBlockEval D Sc cutoff N Λ β))
          (restrict D Sc cutoff N Λ β η) := by
  rw [postCoeff_eq_whiskerLeft, postCoeff_eq_whiskerLeft]
  apply Superfunctor.hom_ext
  intro p M
  change η.app p (Z.obj M) β = (restrict D Sc cutoff N Λ β η).app p (Z.obj M β)
  exact (restrict_app D Sc cutoff N Λ β η p (Z.obj M)).symm

end OddMath.QuiverHecke.ELVOld.WeightCentreBlocks
