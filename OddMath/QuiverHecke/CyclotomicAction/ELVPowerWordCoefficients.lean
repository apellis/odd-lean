import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordWeightContexts
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientModuleMaps

/-! # Coefficient insertion in signed word coordinates

SwappedVacuumCoordinates §§4–6: identify the genuine coefficient module
maps with the signed old-Hom operators before transporting chosen E values.
The full coefficient algebra and chronological multiplication are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordCoefficients
open CyclotomicAction CyclotomicCrossingTensor
universe u
section Generic
variable {C : Type*} [Category* C]
private def conjugate {A B : C} (e : A ≅ B) (f : End B) : End A := e.hom ≫ f ≫ e.inv
private theorem conjugate_square {A B E : C} (e : A ≅ B) (f : B ≅ E)
    (x : End B) (y : End E) (h : x ≫ f.hom = f.hom ≫ y) :
    conjugate e x ≫ (e ≪≫ f).hom = (e ≪≫ f).hom ≫ y := by
  simp only [conjugate, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]
end Generic
private theorem mapped_square {C B : Type*} [Category* C] [Category* B]
    (F : C ⥤ B) {A P : C} {E : B} (e : A ≅ P) (f : F.obj P ≅ E)
    (x : End A) (y : End P) (z : End E)
    (hx : x ≫ e.hom = e.hom ≫ y) (hf : F.map y ≫ f.hom = f.hom ≫ z) :
    F.map x ≫ (F.mapIso e ≪≫ f).hom = (F.mapIso e ≪≫ f).hom ≫ z := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← F.map_comp, hx, F.map_comp, Category.assoc, hf]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The genuine full coefficient module action is the signed old-Hom
operator at every word, including inhomogeneous coefficients. -/
theorem coefficient_fromArrow (ν : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L ν) a =
      PowerWordMorphisms.fromArrow D Sc cutoff L ν ν (coefficientEndomorphism D Sc cutoff ν a) := by
  apply (PowerWordYoneda.homEquiv D Sc cutoff L ν (powerWordObject D Sc cutoff L ν)).injective
  change PowerWordYoneda.evaluate D Sc cutoff L ν (powerWordObject D Sc cutoff L ν)
      (coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L ν) a) =
    PowerWordYoneda.evaluate D Sc cutoff L ν (powerWordObject D Sc cutoff L ν)
      (PowerWordMorphisms.fromArrow D Sc cutoff L ν ν (coefficientEndomorphism D Sc cutoff ν a))
  rw [show PowerWordYoneda.evaluate D Sc cutoff L ν (powerWordObject D Sc cutoff L ν)
      (PowerWordMorphisms.fromArrow D Sc cutoff L ν ν (coefficientEndomorphism D Sc cutoff ν a)) =
    powerWordGenerator D Sc cutoff L ν (OldCategory.mk ν) (coefficientEndomorphism D Sc cutoff ν a) from
      PowerWordYoneda.evaluate_fromElement D Sc cutoff L ν (powerWordObject D Sc cutoff L ν) _]
  change (coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L ν) a).total (OldCategory.mk ν)
    (PowerWordYoneda.unitVector D Sc cutoff L ν) = _
  rw [coefficientModuleAction_total]
  change (powerWordModule D Sc cutoff L ν).map (coefficientEndomorphism D Sc cutoff ν a)
    (powerWordGenerator D Sc cutoff L ν (OldCategory.mk ν) (𝟙 _)) = _
  simpa only [Category.id_comp] using PowerWordYoneda.generator_naturality D Sc cutoff L ν
    (coefficientEndomorphism D Sc cutoff ν a) (𝟙 _)

section Weight
variable [Fintype I] (Λ : X)
local notation "N" => PowerWordContent.powerBound D cutoff L

end Weight
end OddMath.QuiverHecke.ELVOld.PowerWordCoefficients
