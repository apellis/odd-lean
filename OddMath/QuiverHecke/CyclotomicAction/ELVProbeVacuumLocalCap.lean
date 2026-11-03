import OddMath.QuiverHecke.CyclotomicAction.ELVContentVacuumLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierCap
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCoefficientCapUniqueness

/-! # The constructed vacuum local cap on the regular probe

BE (1.14) and SwappedActionAssembly F2: the constructed old vacuum local
record uses exactly the chosen probe induction/right-adjunction/dot fields.
Its raw inverse cap is the prescribed normalized regular-probe row.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u
private theorem family_window_total
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F : Superfunctor k (Superfunctor k C (SVec k)) (Superfunctor k C (SVec k))}
    (a : Superfunctor.id k (Superfunctor k C (SVec k)) ⟶ F)
    (b : F ⟶ Superfunctor.id k (Superfunctor k C (SVec k)))
    (q : Prop) [Decidable q]
    (h : a ≫ b = if q then 𝟙 (Superfunctor.id k (Superfunctor k C (SVec k))) else 0)
    (M : Superfunctor k C (SVec k)) :
    a.total M ≫ b.total M = if q then 𝟙 M else 0 := by
  have hh := congrArg (fun η : Superfunctor.id k (Superfunctor k C (SVec k)) ⟶
    Superfunctor.id k (Superfunctor k C (SVec k)) => η.total M) h
  rw [Superfunctor.comp_total] at hh
  by_cases hq : q
  · rw [ite_eq_left hq] at hh ⊢
    exact hh.trans (SuperNatTrans.id_total (𝟭 (Superfunctor k C (SVec k))) M)
  · rw [ite_eq_right hq] at hh ⊢
    simpa only [SuperNatTrans.total, Superfunctor.zero_app, zero_add] using hh

private theorem module_window_linear
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k))
    (f : (restriction J).obj (induced J M) ⟶ M) (a : ℕ) (q : Prop) [Decidable q]
    (h : unitDotColumn J hα M a ≫ f = if q then 𝟙 M else 0) (w : C) :
    SVec.toLinearMap (f.total w) ∘ₗ unitDotLinear J hα M a w =
      if q then LinearMap.id else 0 := by
  rw [← unitDotColumn_total, ← SVec.toLinearMap_comp, ← Superfunctor.comp_total, h]
  by_cases hq : q
  · rw [ite_eq_left hq, ite_eq_left hq]
    simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one, add_zero]
    rfl
  · rw [ite_eq_right hq, ite_eq_right hq]
    simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add]
    rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ) (i : I)
local notation "cut" => probeCutoff D m
local notation "C₀" => OldContentCategory D Sc cut []
local notation "Z" => zeroModuleCell (k := k) C₀
local notation "A₀" => zeroModuleCellAdjunction (k := k) C₀
local notation "N₀" => probeOldVacuumRegular D Sc m

/-- The constructed local record on the exact probe cells. The ordinary
adjunction and raw dot are retained definitionally, without a Loc premise. -/
def probeVacuumLoc (hP : 0 < cut i) :
    SKM.SuperRouquierLoc A₀ (appendRightAdjunction D Sc m i)
      (0 : End Z) (inductionDotCell D Sc m i)
      (0 : End (Z ≫ inductionCell D Sc m i)) (D.parity i) (-(cut i : ℤ)) :=
  contentVacuumLoc D Sc cut i hP

/-- At the literal regular probe the raw inverse-defined local left cap
is precisely the already prescribed normalized cap, with no compatibility
premise and no additional scalar. -/
theorem probeVacuumLoc_cap_total (hP : 0 < cut i) :
    (probeVacuumLoc D Sc m i hP).capL.total N₀ = cap D Sc m i hP :=
  local_capL_total D Sc m i A₀ (0 : End Z)
    (0 : End (Z ≫ inductionCell D Sc m i)) (probeVacuumLoc D Sc m i hP) hP

omit [Fintype I] in
/-- On every input module the constructed local cap obeys its prescribed
unit-column window, before any scalar coefficient specialization. -/
theorem probeVacuumLoc_cap_unitDotColumn (hP : 0 < cut i)
    (M : Superfunctor k C₀ (SVec k)) (a : ℕ) (ha : a < cut i) :
    unitDotColumn (oldContentAppend D Sc cut [] i)
      (probeOldContentAppendDot_supernatural D Sc m [] i) M a ≫
      (probeVacuumLoc D Sc m i hP).capL.total M =
      if a + 1 = cut i then 𝟙 M else 0 := by
  let L := probeVacuumLoc D Sc m i hP
  have hneg : -(cut i : ℤ) < 0 := by omega
  have ha' : a < (- (-(cut i : ℤ))).toNat := by omega
  have hraw := L.cupD_capL hneg ha'
  have h := family_window_total (L.cupD a) L.capL _ hraw M
  have hu : (L.cupD a).total M = unitDotColumn (oldContentAppend D Sc cut [] i)
      (probeOldContentAppendDot_supernatural D Sc m [] i) M a := by
    change (SKM.RouquierBoundary.cup
      (inductionModuleAdjunction (k := k) (oldContentAppend D Sc cut [] i))
      (inductionModuleDot (oldContentAppend D Sc cut [] i)
        (oldContentAppendDot_supernatural D Sc cut [] i)) a).total M = _
    rw [inductionModuleUnitPower_eq, gridUnitColumnTransformation_total]
  rw [hu] at h
  have he : a = (- (-(cut i : ℤ)) - 1).toNat ↔ a + 1 = cut i := by omega
  simpa only [he] using h

omit [Fintype I] in
/-- Every scalar-evaluating module, including F(E(T0)), has the same
prescribed inverse coefficient cap as the constructed vacuum local record.
The intermediate scalar-evaluation hypothesis is preserved by E and F. -/
theorem probeVacuumLoc_cap_coefficient (hP : 0 < cut i)
    (M : Superfunctor k C₀ (SVec k))
    (hM : ProbeEvaluatesCoefficients D m Sc [] M)
    (r : Fin (contentUnitCount D cut i (([] : List I) : Multiset I)))
    (hr : r.val + 1 = cut i) :
    (probeVacuumLoc D Sc m i hP).capL.total M =
      contentCoefficientCap D Sc cut [] i M
        (contentCrossingHeight_nonneg_of_not_mem D cut [] i (by simp)) r := by
  apply probeContentCoefficientCap_eq_of_window D Sc m [] M hM i (by simp) r
  intro w a ha
  have ha' : a < cut i := by
    simpa only [VacuumCoefficient.count] using ha
  have h := module_window_linear (oldContentAppend D Sc cut [] i)
    (probeOldContentAppendDot_supernatural D Sc m [] i) M _ a _
    (probeVacuumLoc_cap_unitDotColumn D Sc m i hP M a ha') w
  exact h.trans (if_congr (by omega) rfl rfl)

private def vacuumTopSlot (hP : 0 < cut i) :
    Fin (contentUnitCount D cut i (([] : List I) : Multiset I)) :=
  ⟨cut i - 1, by rw [VacuumCoefficient.count]; omega⟩

/-- The actual closure input F(E(T0)) is scalar-evaluating, so its raw
inverse cap is the prescribed native coefficient map with no class premise.
This is the second component required by the left transpose comparison. -/
theorem probeVacuumLoc_cap_FE_coefficient (hP : 0 < cut i) :
    (probeVacuumLoc D Sc m i hP).capL.total
      ((restriction (oldContentAppend D Sc cut [] i)).obj
        (induced (oldContentAppend D Sc cut [] i) N₀)) =
    contentCoefficientCap D Sc cut [] i
      ((restriction (oldContentAppend D Sc cut [] i)).obj
        (induced (oldContentAppend D Sc cut [] i) N₀))
      (contentCrossingHeight_nonneg_of_not_mem D cut [] i (by simp))
      (vacuumTopSlot D m i hP) := by
  have hN : ProbeEvaluatesCoefficients D m Sc [] N₀ :=
    probeOldModule_evaluatesCoefficients D m Sc [] _
  have hE := probeOldInduced_evaluatesCoefficients D m Sc [] i N₀ hN
  have hFE := probeOldRestriction_evaluatesCoefficients D Sc m [] i _ hE
  exact probeVacuumLoc_cap_coefficient D Sc m i hP _ hFE (vacuumTopSlot D m i hP)
    (by change cut i - 1 + 1 = cut i; omega)

end OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
