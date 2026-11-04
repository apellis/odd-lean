import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensorCoefficientMaps

/-! # Tensor coefficients as output-module arrows

SwappedVacuumCoordinates §6: the full tensor-vacuum coefficient acts by
the coefficient arrow of the actual output content category. Even module
charts therefore intertwine both odd and even source coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.TensorCoefficientNaturality
open VacuumTensorCoefficientMaps CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "A" => SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff
local notation "Z" => WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L

/-- The full coefficient arrow in an actual truncated content category. -/
def contentCoefficientArrow {β : Multiset I}
    (c : ContentCategory D Sc cutoff N β) (a : A) : c ⟶ c :=
  (truncatedIdeal D Sc cutoff N c.obj.word c.obj.word).mkQ
    (ELVPScalar.scalar D Sc cutoff c.obj.word a)

/-- The reservoir block action is its own module action on this arrow. -/
theorem vacuumBlockAction_total
    (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) (a : A)
    (c : ContentCategory D Sc cutoff N β.1) :
    (vacuumBlockAction D Sc cutoff L ΛR β a).total c =
      (ReservoirWordValue.initialValue D ΛR Sc cutoff L β).map
        (contentCoefficientArrow D Sc cutoff L c a) := by
  change (coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L []) a).total
    (OldCategory.mk c.obj.word) = _
  rw [coefficientModuleAction_total]
  rfl

/-- The whole-input coefficient is the output module's coefficient map. -/
theorem coefficientAction_output
    (a : A) (M : probeOldWeightSpace D Sc m ΛP (-ΛP))
    (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0))
    (c : ContentCategory D Sc cutoff N β.1) :
    (((VacuumTensorCoefficientMaps.coefficientAction D Sc m cutoff L ΛP ΛR a).total M) β).total c =
      (((Z).obj M) β).map (contentCoefficientArrow D Sc cutoff L c a) := by
  rw [coefficientAction_total, vacuumBlockAction_total]
  rfl

/-- Any even module chart intertwines arbitrary full source coefficients. -/
theorem coefficientAction_evenChart
    (a : SKM.SYM D k) (M : probeOldWeightSpace D Sc m ΛP (-ΛP))
    (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0))
    (T : Superfunctor k (ContentCategory D Sc cutoff N β.1) (SVec k))
    (f : ((Z).obj M) β ⟶ T) (hf : f ∈ parity (R := k) _ _ 0)
    (c : ContentCategory D Sc cutoff N β.1) :
    (((sourceCoefficientAction D Sc m cutoff L ΛP ΛR a).total M) β).total c ≫ f.total c =
      f.total c ≫ T.map (contentCoefficientArrow D Sc cutoff L c
        (SKM.SYM.elvCoefficientQuotient D cutoff a)) := by
  change (((VacuumTensorCoefficientMaps.coefficientAction D Sc m cutoff L ΛP ΛR
    (SKM.SYM.elvCoefficientQuotient D cutoff a)).total M) β).total c ≫ f.total c = _
  rw [coefficientAction_output]
  have htotal (d : ContentCategory D Sc cutoff N β.1) : f.total d = f.app 0 d := by
    rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) d,
      add_zero]
  rw [htotal]
  exact ((Superfunctor.toSuperNatTrans f).isSupernatural 0).naturality_zero _
end OddMath.QuiverHecke.ELVOld.TensorCoefficientNaturality
