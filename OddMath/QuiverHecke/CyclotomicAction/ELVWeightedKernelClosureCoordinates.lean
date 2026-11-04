import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedLocalInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelClosureDegree

/-! # Weighted local closures in raw coefficient coordinates

The closure step G8 evaluates the specified weighted unit, principal inverse,
and cap as the raw represented kernel closure, before applying integer grading.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
private theorem moduleIso_apply {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) (x : F.obj w) :
    moduleIsoLinearEquiv e w x = e.hom.total w x := rfl
private theorem moduleIso_symm_apply {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) (x : G.obj w) :
    (moduleIsoLinearEquiv e w).symm x = e.inv.total w x := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local instance weightedClosurePi : PiSupercategory k
    (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) := supermodulePiSupercategory
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "RM" => weightedRestriction D Sc cutoff N M
local notation "J" => append D Sc cutoff i

/-- The specified local unit principal commutes with the selected source chart. -/
theorem weightedContentUnitPrincipal_chart (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (z : mateTargetSpace D Sc cutoff i RM w) :
    (weightedContentLocalInverseFrom D Sc cutoff N i M (w.word : Multiset I) hh).f'.total
      (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I))
      (weightedMateTargetLinearEquiv D Sc cutoff N i M w z) =
    weightedMateSourceLinearEquiv D Sc cutoff N i M w
      (moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i RM
        (contentUnitCount D cutoff i (w.word : Multiset I))) w
        (((moduleUnitMatrixIso D Sc cutoff RM i w hh).inv z) none)) := by
  have h₀ := weightedContentLocalInverseFrom_principal_total D Sc cutoff N i M
    (w.word : Multiset I) hh
    (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I))
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w z)
  rw [weightedContentUnitInverse_atWord D Sc cutoff N i M w hh] at h₀
  have h₁ := shiftedModuleValueLinearEquiv_hom_coordinate
    ((induction (J)).obj ((restriction (J)).obj RM))
    (induced (T) ((restriction (T)).obj M)) w ((Q).obj w)
    (weightedMateSourceLinearEquiv D Sc cutoff N i M w) (D.parity i)
    (((moduleUnitMatrixIso D Sc cutoff RM i w hh).inv z) none)
  have h₂ := congrArg
    (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
      (induced (T) ((restriction (T)).obj M))).hom.total ((Q).obj w))
    (weightedUnitInverse_none D Sc cutoff N i M w hh z)
  dsimp only [weightedUnitFamilyValueEquiv, induction] at h₂
  dsimp only [induction] at h₁
  simp only [moduleIso_apply, unitMatrixFirstSourceIso]
  dsimp only [induction]
  have h₃ := h₂.symm.trans h₁
  have h₄ := h₀.trans h₃
  convert h₄ using 1

/-- The weighted upper-Hom principal insertion retains its exact parity chart. -/
theorem weightedCapPrincipalInput_coordinates (w : OldCategory D Sc cutoff)
    (m : ℕ) (z : mateTargetSpace D Sc cutoff i RM w) :
    weightedCapMatrixValueEquiv D Sc cutoff N i M m w
      (Pi.single none
        ((moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i RM m) w).symm z)) =
    Pi.single none
      ((((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
        ((restriction (T)).obj (induced (T) M))).inv.total ((Q).obj w))
        (weightedMateTargetLinearEquiv D Sc cutoff N i M w z)) := by
  classical
  apply funext
  intro a
  change weightedCapFamilyValueEquiv D Sc cutoff N i M m w a
    ((Pi.single none
      ((moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i RM m) w).symm z) :
        ∀ a, (capMatrixFamily D Sc cutoff i RM m a).obj w) a) = _
  cases a with
  | none =>
      simp only [Pi.single_eq_same]
      simp only [moduleIso_symm_apply, capMatrixFirstTargetIso]
      dsimp only [weightedCapFamilyValueEquiv]
      have h := shiftedModuleValueLinearEquiv_inv_coordinate
        ((restriction (J)).obj (induced (J) RM))
        ((restriction (T)).obj (induced (T) M)) w ((Q).obj w)
        (weightedMateTargetLinearEquiv D Sc cutoff N i M w) (D.parity i) z
      dsimp only [induction] at h ⊢
      convert h using 1
  | some r =>
      simp only [Pi.single_eq_of_ne (by simp : some r ≠ none), map_zero]

/-- The specified local cap principal commutes with the selected source chart. -/
theorem weightedContentCapPrincipal_chart (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0)
    (z : mateTargetSpace D Sc cutoff i RM w) :
    (weightedContentLocalInverseTo D Sc cutoff N i M (w.word : Multiset I) hh).f'.total
      (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I))
      (weightedMateTargetLinearEquiv D Sc cutoff N i M w z) =
    weightedMateSourceLinearEquiv D Sc cutoff N i M w
      ((moduleCapMatrixIso D Sc cutoff RM i w hh).inv
        (Pi.single none
          ((moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i RM
            (contentCapCount D cutoff i (w.word : Multiset I))) w).symm z))) := by
  have h₀ := weightedContentLocalInverseTo_principal_total D Sc cutoff N i M
    (w.word : Multiset I) hh
    (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I))
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w z)
  rw [weightedContentCapInverse_atWord D Sc cutoff N i M w hh] at h₀
  have h₁ := congrArg (weightedCapMatrixComponentIso D Sc cutoff N i M w hh).inv
    (weightedCapPrincipalInput_coordinates D Sc cutoff N i M w
      (contentCapCount D cutoff i (w.word : Multiset I)) z)
  have h₂ := weightedCapInverse_coordinates D Sc cutoff N i M w hh
    (Pi.single none
      ((moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i RM
        (contentCapCount D cutoff i (w.word : Multiset I))) w).symm z))
  exact h₀.trans (h₁.symm.trans h₂.symm)

/-- The prescribed weighted unit, local unit principal inverse, and cap. -/
def weightedContentUnitClosureValue (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) (b : M.obj w.obj) :=
  (capDotRow (T) (truncatedDot_supernatural D Sc cutoff N i) M s).total w.obj
    ((weightedContentLocalInverseFrom D Sc cutoff N i M β hh).f'.total w
      ((unitDotColumn (T) (truncatedDot_supernatural D Sc cutoff N i) M r).total w.obj b))

/-- The prescribed weighted unit, local cap principal inverse, and cap. -/
def weightedContentCapClosureValue (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) (b : M.obj w.obj) :=
  (capDotRow (T) (truncatedDot_supernatural D Sc cutoff N i) M s).total w.obj
    ((weightedContentLocalInverseTo D Sc cutoff N i M β hh).f'.total w
      ((unitDotColumn (T) (truncatedDot_supernatural D Sc cutoff N i) M r).total w.obj b))

/-- Evaluation of the specified weighted unit closure is the raw represented closure. -/
theorem weightedContentUnitClosureValue_atWord (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (r s : ℕ) (b : (RM).obj w) :
    weightedContentUnitClosureValue D Sc cutoff N i M (w.word : Multiset I) hh
      (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I)) r s b =
    (RM).map (positiveKernelClosure D Sc cutoff i w w hh r s (𝟙 w)) b := by
  unfold weightedContentUnitClosureValue
  rw [← weightedUnitColumnValue_compare D Sc cutoff N i M w r b]
  rw [weightedContentUnitPrincipal_chart D Sc cutoff N i M w hh]
  rw [← weightedCapRowValue_compare D Sc cutoff N i M w s]
  have h := positiveKernelClosure_evaluate D Sc cutoff RM i w w hh r s (𝟙 w) b
  have hi : (RM).map (𝟙 w) b = b :=
    congrArg (fun f : (RM).obj w ⟶ (RM).obj w => f b) ((RM).toFunctor.map_id w)
  rw [hi] at h
  exact h.symm

/-- Evaluation of the specified weighted cap closure is the raw represented closure. -/
theorem weightedContentCapClosureValue_atWord (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0)
    (r s : ℕ) (b : (RM).obj w) :
    weightedContentCapClosureValue D Sc cutoff N i M (w.word : Multiset I) hh
      (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I)) r s b =
    (RM).map (negativeKernelClosure D Sc cutoff i w w hh r s (𝟙 w)) b := by
  unfold weightedContentCapClosureValue
  rw [← weightedUnitColumnValue_compare D Sc cutoff N i M w r b]
  rw [weightedContentCapPrincipal_chart D Sc cutoff N i M w hh]
  rw [← weightedCapRowValue_compare D Sc cutoff N i M w s]
  have h := negativeKernelClosure_evaluate D Sc cutoff RM i w w hh r s (𝟙 w) b
  have hi : (RM).map (𝟙 w) b = b :=
    congrArg (fun f : (RM).obj w ⟶ (RM).obj w => f b) ((RM).toFunctor.map_id w)
  rw [hi] at h
  exact h.symm

end OddMath.QuiverHecke.ELVOld
