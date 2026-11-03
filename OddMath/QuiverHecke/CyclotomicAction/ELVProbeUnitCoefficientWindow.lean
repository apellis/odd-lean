import OddMath.QuiverHecke.CyclotomicAction.ELVProbeUnitInverseRows

/-! # Normalization window of the actual ordinary inverse unit coefficient

The prescribed inverse row extracts its own unit/dot column and kills all
other columns in the finite window. Its canonical source unshift is kept
throughout. This is the ordinary left-cap normalization needed for the
native cap and ground probe functional.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
section GenericWindow
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  (M : Superfunctor k C (SVec k)) (m : ℕ) (w : C)
local instance unitCoefficientWindowPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory
variable (e : unitColumnSourceSpace p M m w ≅ ((restriction J).obj ((induction J).obj M)).obj w)

private theorem inverseWindow_assembled_single {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → SVec k) (X : SVec k) (f : ∀ a, V a ⟶ X) (a : ι) (b : V a) :
    OddMath.FiniteSuperspace.assembleColumns V X f (Pi.single a b) = f a b := by
  change (∑ s, f s ((Pi.single a b : (s : ι) → V s) s)) = _
  rw [Finset.sum_eq_single a]
  · simp
  · intro s _ hs
    rw [Pi.single_eq_of_ne hs]
    exact map_zero _
  · simp

private theorem inverseWindow_matrix_single (a : Fin m)
    (b : ((SKM.homParityShift (k := k) (a.val • p)).obj M).obj w) :
    unitColumnMatrix J hα M m w (Pi.single a b) =
      (shiftedUnitDotColumn J hα M a.val).total w b := by
  classical
  exact inverseWindow_assembled_single
    (fun a : Fin m => ((SKM.homParityShift (k := k) (a.val • p)).obj M).obj w)
    (((restriction J).obj ((induction J).obj M)).obj w)
    (fun a => (shiftedUnitDotColumn J hα M a.val).total w) a b

private theorem inverseWindow_component
    (he : e.hom = unitColumnMatrix J hα M m w) (r : Fin m) (x : unitColumnSourceSpace p M m w) :
    unitColumnInverseRow M w p m e r (unitColumnMatrix J hα M m w x) =
      unitColumnUnshift M w p m r x := by
  have hx := (OddMath.FiniteSuperspace.isoLinearEquiv e).symm_apply_apply x
  change e.inv (e.hom x) = x at hx
  rw [he] at hx
  change ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w
    ((e.inv (unitColumnMatrix J hα M m w x)) r) =
      ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w (x r)
  exact congrArg (fun y => ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w (y r)) hx

private theorem inverseWindow_shifted_unit (n : ℕ) (b : M.obj w) :
    (shiftedUnitDotColumn J hα M n).total w
      ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (n • p)).iso M) w).symm b) =
      unitDotLinear J hα M n w b := by
  have h := LinearMap.congr_fun (shiftedUnitDotColumn_total J hα M n w)
    ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (n • p)).iso M) w).symm b)
  have hz := (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (n • p)).iso M) w).apply_symm_apply b
  change (shiftedUnitDotColumn J hα M n).total w _ =
    unitDotLinear J hα M n w
      ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (n • p)).iso M) w)
        ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (n • p)).iso M) w).symm b)) at h
  exact h.trans (congrArg (unitDotLinear J hα M n w) hz)

private theorem inverseWindow_same (he : e.hom = unitColumnMatrix J hα M m w)
    (r : Fin m) (b : M.obj w) :
    unitColumnInverseRow M w p m e r (unitDotLinear J hα M r.val w b) = b := by
  let es := moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M) w
  have h := inverseWindow_component J hα M m w e he r (Pi.single r (es.symm b))
  rw [inverseWindow_matrix_single, unitColumnUnshift_apply, Pi.single_eq_same] at h
  dsimp only [es] at h
  rw [inverseWindow_shifted_unit] at h
  exact h.trans (es.apply_symm_apply b)

private theorem inverseWindow_other (he : e.hom = unitColumnMatrix J hα M m w)
    (r s : Fin m) (hrs : r ≠ s) (b : M.obj w) :
    unitColumnInverseRow M w p m e r (unitDotLinear J hα M s.val w b) = 0 := by
  let es := moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (s.val • p)).iso M) w
  have h := inverseWindow_component J hα M m w e he r (Pi.single s (es.symm b))
  rw [inverseWindow_matrix_single, unitColumnUnshift_apply, Pi.single_eq_of_ne hrs, map_zero] at h
  dsimp only [es] at h
  rw [inverseWindow_shifted_unit] at h
  exact h

/-- A GIVEN inverse with the prescribed forward unit columns has the exact
Kronecker extraction window. The concrete ordinary inverse below supplies
this intermediate forward-field premise from its proved identification. -/
theorem unitColumnInverseRow_unitDot_window
    (he : e.hom = unitColumnMatrix J hα M m w) (r : Fin m) (a : ℕ) (ha : a < m) :
    SVec.toLinearMap (unitColumnInverseRow M w p m e r) ∘ₗ unitDotLinear J hα M a w =
      if a = r.val then LinearMap.id else 0 := by
  by_cases har : a = r.val
  · rw [ite_eq_left har, har]
    apply LinearMap.ext
    intro b
    exact inverseWindow_same J hα M m w e he r b
  · rw [ite_eq_right har]
    apply LinearMap.ext
    intro b
    exact inverseWindow_other J hα M m w e he r ⟨a, ha⟩ (fun h => har (congrArg Fin.val h).symm) b
end GenericWindow
end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) γ) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc γ N) (i : I) (hi : i ∉ γ)
  (w : OldContentCategory D Sc (probeCutoff D m) γ)
local notation "count" => contentUnitCount D (probeCutoff D m) i (γ : Multiset I)
local notation "S" => probeOrdinaryAppend D Sc m γ i
local notation "U" => probeOldOrdinaryFunctor D Sc m γ
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m γ N hN

/-- The actual ordinary inverse coefficient extracts its prescribed dot
power and kills every other power in the finite unit window. -/
theorem probeMissingColourUnitCoefficient_unitDot (r : Fin count) (a : ℕ) (ha : a < count) :
    SVec.toLinearMap (probeMissingColourUnitCoefficient D Sc m γ N hN i hi w r) ∘ₗ
      unitDotLinear S (probeOrdinaryAppendDot_supernatural D Sc m γ i) O a ((U).obj w) =
    if a = r.val then LinearMap.id else 0 := by
  have h := unitColumnInverseRow_unitDot_window S (probeOrdinaryAppendDot_supernatural D Sc m γ i)
    O count ((U).obj w) (probeMissingColourUnitMatrixIso D Sc m γ N hN i hi w)
    (probeMissingColourUnitMatrixIso_hom D Sc m γ N hN i hi w) r a ha
  exact h
end OddMath.QuiverHecke
