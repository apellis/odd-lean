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
private theorem eqEndAction_ne_zero {F G : C} (h : F = G) (f : End F) (hf : f ≠ 0) :
    eqEndAction (k := k) h f ≠ 0 := by
  subst G
  exact hf
private theorem map_eq_zero_of_id (F : C ⥤ C) (hF : F = 𝟭 C)
    {A B : C} (f : A ⟶ B) (h : F.map f = 0) : f = 0 := by
  subst F
  exact h
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

private theorem reindexAction_ne_zero {x y : X} (h : x = y)
    (F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x)
    (φ : SKM.SYM D k →ₐ[k] End F) (a : SKM.SYM D k) (ha : φ a ≠ 0) :
    reindexAction D Sc m cutoff L ΛP ΛR h F φ a ≠ 0 := by
  subst y
  exact ha

private theorem nilPathAction_ne_zero (a : SKM.SYM D k)
    (ha : sourceCoefficientAction D Sc m cutoff L ΛP ΛR a ≠ 0) :
    pathCoefficientAction D Sc m cutoff L ΛP ΛR (SPath.nil (0,0))
      (by simp) a ≠ 0 := by
  intro hz
  apply ha
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  have h := congrArg (fun f => f.total M) hz
  rw [pathCoefficientAction_total] at h
  have hzero : (0 : End (TensorReservoirWords.pathHom D Sc m cutoff L ΛP ΛR
      (SPath.nil (0,0)) (by simp))).total M = 0 :=
    (supernaturalTotalLinearMap _ _ M).map_zero
  rw [hzero] at h
  have hf := map_eq_zero_of_id
    (ReservoirWord.word W ΛR (SPath.nil (0,0)) (by simp)).toFunctor
    (congrArg Superfunctor.toFunctor (ReservoirWord.word_nil W ΛR 0))
    ((sourceCoefficientAction D Sc m cutoff L ΛP ΛR a).total M) h
  exact hf.trans (supernaturalTotalLinearMap Z Z M).map_zero.symm

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

/-- The normalized empty word retains every nonzero whole-input source map. -/
theorem wordAction_nil_ne_zero (a : SKM.SYM D k)
    (ha : sourceCoefficientAction D Sc m cutoff L ΛP ΛR a ≠ 0) :
    wordAction D Sc m cutoff L ΛP ΛR [] a ≠ 0 := by
  have h : initialAction D Sc m cutoff L ΛP ΛR a ≠ 0 := by
    apply eqEndAction_ne_zero
    apply reindexAction_ne_zero D Sc m cutoff L ΛP ΛR
    exact nilPathAction_ne_zero D Sc m cutoff L ΛP ΛR a ha
  simpa only [wordAction, List.reverseRecOn_nil] using h

/-- Every full word Hom gets the same original coefficient algebra by postcomposition. -/
def wordHomAction (ν : List I)
    (G : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
      elvWeightSpace D Sc cutoff N ΛR (PowerWordWeight.wordWeight D ΛR ν)) :
    SKM.SYM D k →ₐ[k] Module.End k (G ⟶ TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν) :=
  (postcompositionAlgHom G (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν)).comp
    (wordAction D Sc m cutoff L ΛP ΛR ν)
end OddMath.QuiverHecke.ELVOld.TensorWordCoefficientAction
