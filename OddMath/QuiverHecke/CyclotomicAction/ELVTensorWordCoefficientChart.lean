import OddMath.QuiverHecke.CyclotomicAction.ELVTensorPathCoefficientCoherence
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorCoefficientNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorPairChartCoherence

/-! # Tensor word charts and full source coefficients

SwappedVacuumCoordinates §6: the prescribed global tensor-word chart
intertwines the full source coefficient with its signed old-Hom arrow.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.TensorWordCoefficientChart
open CyclotomicAction SwappedAssembly VacuumTensorCoefficientMaps TensorWordCoefficientAction
open TensorPathCoefficientCoherence TensorCoefficientNaturality
universe u
private theorem mapped_square {C B : Type*} [Category* C] [Category* B]
    (F : C ⥤ B) {A P : C} {E : B} (e : A ≅ P) (f : F.obj P ≅ E)
    (x : End A) (y : End P) (z : End E)
    (hx : x ≫ e.hom = e.hom ≫ y) (hf : F.map y ≫ f.hom = f.hom ≫ z) :
    F.map x ≫ (F.mapIso e ≪≫ f).hom = (F.mapIso e ≪≫ f).hom ≫ z := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← F.map_comp, hx, F.map_comp, Category.assoc, hf]
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P₀" => WeightTensorVacuum.regularProbe D Sc m ΛP
local notation "Z" => WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L
local notation "A" => SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff

/-- The signed old-Hom coefficient arrow acts by the same output coefficient. -/
theorem wordFamilyArrow_total (x : X) (ν : List I) (a : A)
    (β : WeightBlocks D ΛR x) (c : ContentCategory D Sc cutoff N β.1) :
    (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR x ν ν
      (coefficientEndomorphism D Sc cutoff ν a) β).total c =
    (PowerWordWeight.wordFamily D Sc cutoff L ΛR x ν β).map
      (contentCoefficientArrow D Sc cutoff L c a) := by
  change (PowerWordContentCross.contentWordArrow D Sc cutoff L β.1 ν ν
    (coefficientEndomorphism D Sc cutoff ν a)).total c = _
  rw [PowerWordContentCross.contentWordArrow_total, ← PowerWordCoefficients.coefficient_fromArrow,
    coefficientModuleAction_total]
  rfl

private theorem nilHom_heq :
    HEq (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR []) Z := by
  apply (TensorReservoirWords.pathHom_heq D Sc m cutoff L ΛP ΛR (SPath.nil (0,0)) (by simp)).symm.trans
  change HEq (Z ≫ ReservoirWord.word (elvRouquierData D Sc cutoff N ΛR) ΛR
    (SPath.nil (0,0)) (by simp)) Z
  rw [ReservoirWord.word_nil]
  rfl

private theorem nilAction_heq (a : SKM.SYM D k) :
    HEq (wordAction D Sc m cutoff L ΛP ΛR [] a)
      (sourceCoefficientAction D Sc m cutoff L ΛP ΛR a) := by
  apply (wordAction_nil_heq D Sc m cutoff L ΛP ΛR a).trans
  have hg : ∀ (G : elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR 0) ⟶
      elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR 0)), G = 𝟙 _ →
      HEq (Superfunctor.whiskerRight (sourceCoefficientAction D Sc m cutoff L ΛP ΛR a) G)
        (sourceCoefficientAction D Sc m cutoff L ΛP ΛR a) := by
    intro G h
    subst G
    apply heq_of_eq
    apply Superfunctor.hom_ext
    intro q M
    rfl
  exact hg _ (ReservoirWord.word_nil _ ΛR 0)

private theorem output_transport {x y : X} (h : x = y)
    {F : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x}
    {F' : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR y}
    (hF : HEq F F') {f : End F} {f' : End F'} (hf : HEq f f') (a : A)
    (hout : ∀ (β : WeightBlocks D ΛR x) (c : ContentCategory D Sc cutoff N β.1),
      ((f.total P₀) β).total c = ((F.obj P₀) β).map (contentCoefficientArrow D Sc cutoff L c a)) :
    ∀ (β : WeightBlocks D ΛR y) (c : ContentCategory D Sc cutoff N β.1),
      ((f'.total P₀) β).total c = ((F'.obj P₀) β).map (contentCoefficientArrow D Sc cutoff L c a) := by
  cases h
  cases hF
  cases hf
  exact hout

/-- The normalized empty-word action is still the output coefficient action. -/
theorem wordAction_nil_output (a : SKM.SYM D k)
    (β : WeightBlocks D ΛR (PowerWordWeight.wordWeight D ΛR []))
    (c : ContentCategory D Sc cutoff N β.1) :
    (((wordAction D Sc m cutoff L ΛP ΛR [] a).total P₀) β).total c =
      (((TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR []).obj P₀) β).map
        (contentCoefficientArrow D Sc cutoff L c (SKM.SYM.elvCoefficientQuotient D cutoff a)) := by
  exact output_transport D Sc m cutoff L ΛP ΛR
    (TensorReservoirWords.path_weight D ΛR (SPath.nil (0,0)) (by simp))
    (nilHom_heq D Sc m cutoff L ΛP ΛR).symm (nilAction_heq D Sc m cutoff L ΛP ΛR a).symm
    (SKM.SYM.elvCoefficientQuotient D cutoff a)
    (fun β c => coefficientAction_output D Sc m cutoff L ΛP ΛR
      (SKM.SYM.elvCoefficientQuotient D cutoff a) P₀ β c) β c

/-- The global empty-word chart intertwines every raw source coefficient. -/
theorem chart_nil_square (a : SKM.SYM D k) :
    (wordAction D Sc m cutoff L ΛP ΛR [] a).total P₀ ≫
      (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR []).hom =
    (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR []).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR
        (PowerWordWeight.wordWeight D ΛR []) [] []
        (coefficientEndomorphism D Sc cutoff [] (SKM.SYM.elvCoefficientQuotient D cutoff a)) := by
  funext β
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro c
  change (((wordAction D Sc m cutoff L ΛP ΛR [] a).total P₀) β ≫
    (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR []).hom β).total c = _
  rw [Superfunctor.comp_total, wordAction_nil_output]
  change _ = (((TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR []).hom β ≫
    PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR
      (PowerWordWeight.wordWeight D ΛR []) [] []
      (coefficientEndomorphism D Sc cutoff [] (SKM.SYM.elvCoefficientQuotient D cutoff a)) β).total c)
  rw [Superfunctor.comp_total, wordFamilyArrow_total]
  let f := (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR []).hom β
  have hf : f ∈ parity (R := k) _ _ 0 := TensorVacuumWords.chart_even D Sc m cutoff L ΛP ΛR [] β
  have htotal : f.total c = f.app 0 c := by
    rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  change _ ≫ f.total c = f.total c ≫ _
  rw [htotal]
  exact ((Superfunctor.toSuperNatTrans f).isSupernatural 0).naturality_zero _

private theorem square_transport
    {x : X}
    {F G : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x}
    (h : F = G) {f : End F} {g : End G} (hf : HEq f g)
    {T : ELVWeightProduct D Sc cutoff N ΛR x}
    (cF : F.obj P₀ ⟶ T) (cG : G.obj P₀ ⟶ T) (hc : HEq cF cG) (z : End T)
    (hs : f.total P₀ ≫ cF = cF ≫ z) : g.total P₀ ≫ cG = cG ≫ z := by
  cases h
  cases hf
  cases hc
  exact hs

private theorem dotChart_hom (ν : List I) (i : I) :
    (TensorVacuumWords.dotChart D Sc m cutoff L ΛP ΛR ν i).hom =
      (elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i)).map
        (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR ν).hom ≫
          (PowerWordWeight.weightAppendIso D Sc cutoff L ΛR ν i).hom := by
  simp only [TensorVacuumWords.dotChart, TensorVacuumWords.chart, PowerWordEvaluation.appendChart,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]

/-- The prescribed global word chart intertwines the entire raw source
coefficient action with the signed original coefficient arrow. -/
theorem chart_square (ν : List I) (a : SKM.SYM D k) :
    (wordAction D Sc m cutoff L ΛP ΛR ν a).total P₀ ≫
      (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR ν).hom =
    (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR ν).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR
        (PowerWordWeight.wordWeight D ΛR ν) ν ν
        (coefficientEndomorphism D Sc cutoff ν (SKM.SYM.elvCoefficientQuotient D cutoff a)) := by
  induction ν using List.reverseRecOn with
  | nil => exact chart_nil_square D Sc m cutoff L ΛP ΛR a
  | append_singleton ν i ih =>
    let E := elvE D Sc cutoff N i ΛR (PowerWordWeight.wordWeight_append D ΛR ν i)
    let f := wordAction D Sc m cutoff L ΛP ΛR ν a
    have ha := PowerWordWeightWhiskering.append_family_arrow D Sc cutoff L ΛR ν ν i
      (PowerWordWeight.wordWeight D ΛR ν) (PowerWordWeight.wordWeight D ΛR (ν ++ [i]))
      rfl rfl rfl rfl (PowerWordWeight.wordWeight_append D ΛR ν i) rfl
      (coefficientEndomorphism D Sc cutoff ν (SKM.SYM.elvCoefficientQuotient D cutoff a))
    rw [append_coefficientEndomorphism] at ha
    have hs : E.map (f.total P₀) ≫ (TensorVacuumWords.dotChart D Sc m cutoff L ΛP ΛR ν i).hom =
        (TensorVacuumWords.dotChart D Sc m cutoff L ΛP ΛR ν i).hom ≫
          PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR
            (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) (ν ++ [i]) (ν ++ [i])
            (coefficientEndomorphism D Sc cutoff (ν ++ [i])
              (SKM.SYM.elvCoefficientQuotient D cutoff a)) := by
      rw [dotChart_hom]
      simpa only [Iso.trans_hom, Functor.mapIso_hom] using
        (mapped_square E.toFunctor (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR ν)
          (PowerWordWeight.weightAppendIso D Sc cutoff L ΛR ν i) _ _ _ ih ha)
    have ht : (Superfunctor.whiskerRight f E).total P₀ = E.map (f.total P₀) := by
      change E.map (f.app 0 P₀) + E.map (f.app 1 P₀) = E.map (f.app 0 P₀ + f.app 1 P₀)
      exact E.toFunctor.map_add.symm
    rw [← ht] at hs
    exact square_transport D Sc m cutoff L ΛP ΛR
      (TensorVacuumWords.wordHom_append D Sc m cutoff L ΛP ΛR ν i).symm
      (wordAction_append_heq D Sc m cutoff L ΛP ΛR ν i a).symm
      (TensorVacuumWords.dotChart D Sc m cutoff L ΛP ΛR ν i).hom
      (TensorVacuumWords.chart D Sc m cutoff L ΛP ΛR (ν ++ [i])).hom
      (TensorVacuumWords.chart_append_heq D Sc m cutoff L ΛP ΛR ν i).symm _ hs

end OddMath.QuiverHecke.ELVOld.TensorWordCoefficientChart
