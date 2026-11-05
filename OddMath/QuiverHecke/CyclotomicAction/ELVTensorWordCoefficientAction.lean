import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensorCoefficientMaps
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorWordChartCoherence

/-! # Source coefficients on the whole tensor E-word

SwappedVacuumCoordinates §§2–6: the source coefficient endomorphism is
whiskered through each prescribed E functor on the full tensor Hom. The
normalizing word equalities are transported by their specified isomorphisms.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.TensorWordCoefficientAction
open CyclotomicAction SwappedAssembly VacuumTensorCoefficientMaps
universe u
section Generic
variable {k : Type*} [CommRing k] {C : Type*} [Category* C] [Preadditive C] [Linear k C]
private def eqEndAction {F G : C} (h : F = G) : End F →ₐ[k] End G := by
  subst G
  exact AlgHom.id k (End F)
private theorem eqEndAction_apply {F G : C} (h : F = G) (f : End F) :
    eqEndAction (k := k) h f = eqToHom h.symm ≫ f ≫ eqToHom h := by
  subst G
  simp only [eqEndAction, AlgHom.id_apply, eqToHom_refl, Category.id_comp, Category.comp_id]
end Generic
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "R" => WeightTensorVacuum.regularProbe D Sc m ΛP
local notation "W" => elvRouquierData D Sc cutoff N ΛR
local notation "Z" => WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L

private def reindexAction {x y : X} (h : x = y)
    (F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x)
    (a : SKM.SYM D k →ₐ[k] End F) :
    SKM.SYM D k →ₐ[k] End (h ▸ F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
      elvWeightSpace D Sc cutoff N ΛR y) := by
  subst y
  exact a

private def initialAction : SKM.SYM D k →ₐ[k] End (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR []) :=
  (eqEndAction (TensorReservoirWords.pathHomAt_eq_wordHom D Sc m cutoff L ΛP ΛR
    (SPath.nil (0,0)) (by simp))).comp
      (reindexAction D Sc m cutoff L ΛP ΛR
        (TensorReservoirWords.path_weight D ΛR (SPath.nil (0,0)) (by simp))
        (TensorReservoirWords.pathHom D Sc m cutoff L ΛP ΛR (SPath.nil (0,0)) (by simp))
        (pathCoefficientAction D Sc m cutoff L ΛP ΛR (SPath.nil (0,0)) (by simp)))

/-- The source action on a whole E-word is literal right whiskering of
the selected full-input tensor action at every append step. -/
def wordAction (ν : List I) : SKM.SYM D k →ₐ[k]
    End (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν) :=
  ν.reverseRecOn (initialAction D Sc m cutoff L ΛP ΛR)
    (fun ρ i a =>
      (eqEndAction (TensorVacuumWords.wordHom_append D Sc m cutoff L ΛP ΛR ρ i).symm).comp
        ((postwhiskerEndAction (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ρ)
          (elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ρ i))).comp a))

/-- Append preserves the literal full supernatural coefficient, with
only the given whole-Hom equality inserted around the map. -/
theorem wordAction_append (ν : List I) (i : I) (a : SKM.SYM D k) :
    wordAction D Sc m cutoff L ΛP ΛR (ν ++ [i]) a =
      eqToHom (TensorVacuumWords.wordHom_append D Sc m cutoff L ΛP ΛR ν i) ≫
        Superfunctor.whiskerRight (wordAction D Sc m cutoff L ΛP ΛR ν a)
          (elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i)) ≫
            eqToHom (TensorVacuumWords.wordHom_append D Sc m cutoff L ΛP ΛR ν i).symm := by
  simp only [wordAction, List.reverseRecOn_concat, AlgHom.comp_apply, eqEndAction_apply]
  rfl

end OddMath.QuiverHecke.ELVOld.TensorWordCoefficientAction
