import OddMath.QuiverHecke.CyclotomicAction.WeightedMatrix
import OddMath.QuiverHecke.CyclotomicAction.KernelEntryDegrees
import OddMath.QuiverHecke.CyclotomicAction.ContentBlockMatrix
import OddMath.Algebra.FiniteSupermoduleCoordinates
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts
import OddMath.QuiverHecke.CyclotomicAction.ContentBlockExtension
import OddMath.QuiverHecke.CyclotomicAction.CoefficientPowerSeries
import OddMath.QuiverHecke.CyclotomicAction.CoefficientPowerAnnihilation

/-!
# Weighted kernel

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Inverse coordinates for the actual weighted and OLD finite matrices

Inverse uniqueness applied to the checked forward squares identifies the
independently constructed weighted inverse with the selected OLD inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction TensorMatrixCoordinates
universe u
private theorem inverse_square {k : Type u} [CommRing k] {V W V' W' : SVec k}
    (e : V ≅ W) (e' : V' ≅ W') (a : V ≃ₗ[k] V') (b : W ≃ₗ[k] W')
    (h : b.toLinearMap ∘ₗ e.hom = e'.hom ∘ₗ a.toLinearMap) (z : W) :
    a (e.inv z) = e'.inv (b z) := by
  have hleft (y : V') : e'.inv (e'.hom y) = y :=
    congrArg (fun f : V' ⟶ V' => f y) e'.hom_inv_id
  have hright : e.hom (e.inv z) = z :=
    congrArg (fun f : W ⟶ W => f z) e.inv_hom_id
  have hs : b (e.hom (e.inv z)) = e'.hom (a (e.inv z)) := LinearMap.congr_fun h (e.inv z)
  calc
    _ = e'.inv (e'.hom (a (e.inv z))) := (hleft _).symm
    _ = e'.inv (b (e.hom (e.inv z))) := congrArg e'.inv hs.symm
    _ = _ := congrArg (fun y => e'.inv (b y)) hright

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The actual unit inverse commutes with the full finite parity coordinate chart. -/
theorem weightedUnitInverse_coordinates (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (z : mateTargetSpace D Sc cutoff i RM w) :
    weightedUnitMatrixValueEquiv D Sc cutoff N i M _ w
      ((moduleUnitMatrixIso D Sc cutoff RM i w hh).inv z) =
    (weightedUnitMatrixComponentIso D Sc cutoff N i M w hh).inv
      (weightedMateTargetLinearEquiv D Sc cutoff N i M w z) := by
  apply inverse_square (moduleUnitMatrixIso D Sc cutoff RM i w hh)
    (weightedUnitMatrixComponentIso D Sc cutoff N i M w hh)
  dsimp only [weightedUnitMatrixArrow, Arrow.mk, Arrow.left, Arrow.right] at *
  rw [moduleUnitMatrixIso_hom,weightedUnitMatrixComponentIso_hom]
  exact weightedMatrixCharts_unitMatrix D Sc cutoff N i M (contentUnitCount D cutoff i (w.word : Multiset I)) w

/-- The actual cap inverse commutes with the full finite parity coordinate chart. -/
theorem weightedCapInverse_coordinates (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0)
    (z : capMatrixTargetSpace D Sc cutoff i RM (contentCapCount D cutoff i (w.word : Multiset I)) w) :
    weightedMateSourceLinearEquiv D Sc cutoff N i M w
      ((moduleCapMatrixIso D Sc cutoff RM i w hh).inv z) =
    (weightedCapMatrixComponentIso D Sc cutoff N i M w hh).inv
      (weightedCapMatrixValueEquiv D Sc cutoff N i M _ w z) := by
  apply inverse_square (moduleCapMatrixIso D Sc cutoff RM i w hh)
    (weightedCapMatrixComponentIso D Sc cutoff N i M w hh)
  dsimp only [weightedCapMatrixArrow, Arrow.mk, Arrow.left, Arrow.right] at *
  rw [moduleCapMatrixIso_hom,weightedCapMatrixComponentIso_hom]
  exact weightedMatrixCharts_capMatrix D Sc cutoff N i M (contentCapCount D cutoff i (w.word : Multiset I)) w

/-- In particular, the principal unit inverse slot is retained literally. -/
theorem weightedUnitInverse_none (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (z : mateTargetSpace D Sc cutoff i RM w) :
    weightedUnitFamilyValueEquiv D Sc cutoff N i M _ w none
      (((moduleUnitMatrixIso D Sc cutoff RM i w hh).inv z) none) =
    ((weightedUnitMatrixComponentIso D Sc cutoff N i M w hh).inv
      (weightedMateTargetLinearEquiv D Sc cutoff N i M w z)) none :=
  congrFun (weightedUnitInverse_coordinates D Sc cutoff N i M w hh z) none

private def isoLinear {V W : SVec k} (e : V ≅ W) : V ≃ₗ[k] W where
  toLinearMap := e.hom
  invFun := e.inv
  left_inv z := congrArg (fun f : V ⟶ V => f z) e.hom_inv_id
  right_inv z := congrArg (fun f : W ⟶ W => f z) e.inv_hom_id

private theorem inverse_total {C : Type u} [Category.{u} C] [Preadditive C]
    [Linear k C] [Supercategory k C] {F G : Superfunctor k C (SVec k)}
    (e : F ≅ G) (w : C) (e' : F.obj w ≅ G.obj w)
    (h : e.hom.total w = e'.hom) : e.inv.total w = e'.inv := by
  have he : moduleIsoLinearEquiv e w = isoLinear e' := by
    apply LinearEquiv.toLinearMap_injective
    exact h
  exact congrArg (fun f => f.symm.toLinearMap) he

/-- Evaluation of the exact-content unit inverse is the independently built
weighted component inverse, at the original word and its prescribed count. -/
theorem weightedContentUnitInverse_atWord (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I)) :
    (weightedContentUnitMatrixIso D Sc cutoff N i M (w.word : Multiset I) hh).inv.total
      (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I)) =
    (weightedUnitMatrixComponentIso D Sc cutoff N i M w hh).inv := by
  apply inverse_total
  rw [weightedContentUnitMatrixIso_hom_total,weightedUnitMatrixComponentIso_hom]

/-- The same identification for the exact-content cap inverse. -/
theorem weightedContentCapInverse_atWord (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0) :
    (weightedContentCapMatrixIso D Sc cutoff N i M (w.word : Multiset I) hh).inv.total
      (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I)) =
    (weightedCapMatrixComponentIso D Sc cutoff N i M w hh).inv := by
  apply inverse_total
  rw [weightedContentCapMatrixIso_hom_total,weightedCapMatrixComponentIso_hom]

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Principal entries of the specified weighted local inverses

BE (1.13)–(1.14): evaluation retains the principal projection or insertion
of the same finite content matrix inverse, with its named parity isomorphism.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction OddMath.FiniteSupermodule CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) (β : Multiset I)
local instance weightedPrincipalPi : PiSupercategory k
    (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) := supermodulePiSupercategory
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "R" => restriction (contentInclusion D Sc cutoff N β)

/-- The unit local principal is the actual inverse's literal `none` row. -/
theorem weightedContentLocalInverseFrom_principal_total
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (z : ((restriction (T)).obj (induced (T) M)).obj w.obj) :
    (weightedContentLocalInverseFrom D Sc cutoff N i M β hh).f'.total w z =
      (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso (induced (T) ((restriction (T)).obj M))).hom.total w.obj)
        (((weightedContentUnitMatrixIso D Sc cutoff N i M β hh).inv.total w z) none) := by
  dsimp only [weightedContentLocalInverseFrom, localInverseFromColumns,
    inverseCoordinateRow, optionRestoringIso]
  simp only [Iso.trans_inv, eqToIso.inv]
  dsimp only [restriction_finiteProduct]
  simp only [eqToHom_refl, Category.comp_id, Superfunctor.comp_total]
  change (((R).mapIso ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
    (induced (T) ((restriction (T)).obj M)))).hom.total w)
      ((projectionHom (fun a => (R).obj (weightedUnitMatrixFamily D Sc cutoff N i M
        (contentUnitCount D cutoff i β) a)) none).total w
        ((weightedContentUnitMatrixIso D Sc cutoff N i M β hh).inv.total w z)) = _
  rw [projectionHom_total_apply]
  rfl

/-- The cap local principal is the actual inverse's literal `none` column. -/
theorem weightedContentLocalInverseTo_principal_total
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (z : ((restriction (T)).obj (induced (T) M)).obj w.obj) :
    (weightedContentLocalInverseTo D Sc cutoff N i M β hh).f'.total w z =
      (weightedContentCapMatrixIso D Sc cutoff N i M β hh).inv.total w
        (Pi.single none
          ((((SKM.homParityShiftDatum (k := k) (D.parity i)).iso ((restriction (T)).obj (induced (T) M))).inv.total w.obj) z)) := by
  dsimp only [weightedContentLocalInverseTo, localInverseToRows,
    inverseCoordinateColumn, optionRestoringIso]
  simp only [Iso.trans_inv, eqToIso.inv]
  dsimp only [restriction_finiteProduct]
  simp only [eqToHom_refl, Category.id_comp, Superfunctor.comp_total]
  change (weightedContentCapMatrixIso D Sc cutoff N i M β hh).inv.total w
    ((inclusionHom (fun a => (R).obj (weightedCapMatrixFamily D Sc cutoff N i M
        (contentCapCount D cutoff i β) a)) none).total w
      ((((R).mapIso ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
        ((restriction (T)).obj (induced (T) M)))).inv.total w) z)) = _
  congr 1
  apply funext
  intro a
  cases a with
  | none =>
      simp only [inclusionHom_total_self, Pi.single_eq_same]
      rfl
  | some a =>
      rw [inclusionHom_total_ne _ none (some a) (Ne.symm (Option.some_ne_none a))]
      symm
      apply Pi.single_eq_of_ne
      exact Option.some_ne_none a

end OddMath.QuiverHecke.ELVOld
end

end

section

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
end

end

section

/-! # Weighted kernel closure evaluation at arbitrary stored content

The G8 coefficient attachment retains arbitrary stored content and evaluates
the literal weighted local closure by the truncated raw kernel coefficient.
-/
noncomputable section
set_option backward.dsimp.instances true
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u v
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

attribute [local irreducible] positiveKernelClosure negativeKernelClosure
  weightedContentUnitClosureValue weightedContentCapClosureValue

private def contentRec
    {P : ∀ β : Multiset I, ContentCategory D Sc cutoff N β → Sort v}
    (h : ∀ l : List I,
      P (l : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩)
    (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : P β w := by
  rcases w with ⟨t, ht⟩
  cases ht
  exact h t.word

private theorem contentRec_atWord
    {P : ∀ β : Multiset I, ContentCategory D Sc cutoff N β → Sort v}
    (h : ∀ l : List I,
      P (l : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩)
    (l : List I) :
    contentRec D Sc cutoff N h (l : Multiset I)
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ = h l := rfl

private def unitWordCoefficient (l : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I)) (r s : ℕ) :
    (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ ⟶
      (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ :=
  truncateOld D Sc cutoff N l l
    (positiveKernelClosure D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _))

private def capWordCoefficient (l : List I)
    (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0) (r s : ℕ) :
    (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ ⟶
      (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ :=
  truncateOld D Sc cutoff N l l
    (negativeKernelClosure D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _))

/-- The represented source endomorphism for the prescribed unit closure. -/
def weightedContentUnitClosureCoefficient (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) : w.obj ⟶ w.obj :=
  contentRec D Sc cutoff N
    (P := fun β w => (0 ≤ contentCrossingHeight D cutoff i β) → ℕ → ℕ → (w.obj ⟶ w.obj))
    (unitWordCoefficient D Sc cutoff N i) β w hh r s

/-- The represented source endomorphism for the prescribed cap closure. -/
def weightedContentCapClosureCoefficient (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) : w.obj ⟶ w.obj :=
  contentRec D Sc cutoff N
    (P := fun β w => (contentCrossingHeight D cutoff i β ≤ 0) → ℕ → ℕ → (w.obj ⟶ w.obj))
    (capWordCoefficient D Sc cutoff N i) β w hh r s

private theorem unitCoefficient_atWord (l : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I)) (r s : ℕ) :
    weightedContentUnitClosureCoefficient D Sc cutoff N i (l : Multiset I) hh
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s =
    unitWordCoefficient D Sc cutoff N i l hh r s := by
  exact congrFun (congrFun (congrFun
    (contentRec_atWord D Sc cutoff N
      (P := fun β w => (0 ≤ contentCrossingHeight D cutoff i β) → ℕ → ℕ → (w.obj ⟶ w.obj))
      (unitWordCoefficient D Sc cutoff N i) l) hh) r) s

private theorem capCoefficient_atWord (l : List I)
    (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0) (r s : ℕ) :
    weightedContentCapClosureCoefficient D Sc cutoff N i (l : Multiset I) hh
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s =
    capWordCoefficient D Sc cutoff N i l hh r s := by
  exact congrFun (congrFun (congrFun
    (contentRec_atWord D Sc cutoff N
      (P := fun β w => (contentCrossingHeight D cutoff i β ≤ 0) → ℕ → ℕ → (w.obj ⟶ w.obj))
      (capWordCoefficient D Sc cutoff N i) l) hh) r) s

private theorem restriction_map_value (t w : OldCategory D Sc cutoff) (f : t ⟶ w)
    (b : (RM).obj t) :
    (RM).map f b = M.map (X := (oldTruncateFunctor D Sc cutoff N).obj t)
      (Y := (oldTruncateFunctor D Sc cutoff N).obj w)
      ((oldTruncateFunctor D Sc cutoff N).map f) b := rfl
private theorem quotient_map_value (t w : OldCategory D Sc cutoff) (f : t ⟶ w) :
    (oldTruncateFunctor D Sc cutoff N).map f =
      truncateOld D Sc cutoff N t.word w.word f := rfl

private theorem restriction_truncate_value (t w : OldCategory D Sc cutoff) (f : t ⟶ w)
    (b : (RM).obj t) :
    (RM).map f b = M.map (X := (oldTruncateFunctor D Sc cutoff N).obj t)
      (Y := (oldTruncateFunctor D Sc cutoff N).obj w)
      (truncateOld D Sc cutoff N t.word w.word f) b := by
  exact (restriction_map_value D Sc cutoff N M t w f b).trans
    (congrArg (fun a : (oldTruncateFunctor D Sc cutoff N).obj t ⟶
      (oldTruncateFunctor D Sc cutoff N).obj w =>
        M.map (X := (oldTruncateFunctor D Sc cutoff N).obj t)
          (Y := (oldTruncateFunctor D Sc cutoff N).obj w) a b)
      (quotient_map_value D Sc cutoff N t w f))

private theorem unit_atWord_raw (l : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I))
    (r s : ℕ) (b : (RM).obj ⟨l⟩) :
    weightedContentUnitClosureValue D Sc cutoff N i M (l : Multiset I) hh
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s b =
    M.map (X := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
      (Y := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
      (unitWordCoefficient D Sc cutoff N i l hh r s) b := by
  exact (weightedContentUnitClosureValue_atWord D Sc cutoff N i M ⟨l⟩ hh r s b).trans
    (restriction_truncate_value D Sc cutoff N M ⟨l⟩ ⟨l⟩
      (positiveKernelClosure D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _)) b)

private theorem cap_atWord_raw (l : List I)
    (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0)
    (r s : ℕ) (b : (RM).obj ⟨l⟩) :
    weightedContentCapClosureValue D Sc cutoff N i M (l : Multiset I) hh
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s b =
    M.map (X := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
      (Y := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
      (capWordCoefficient D Sc cutoff N i l hh r s) b := by
  exact (weightedContentCapClosureValue_atWord D Sc cutoff N i M ⟨l⟩ hh r s b).trans
    (restriction_truncate_value D Sc cutoff N M ⟨l⟩ ⟨l⟩
      (negativeKernelClosure D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _)) b)

attribute [local irreducible] unitWordCoefficient capWordCoefficient
  weightedContentUnitClosureCoefficient weightedContentCapClosureCoefficient

private def UnitEvaluation (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : Prop :=
  ∀ (hh : 0 ≤ contentCrossingHeight D cutoff i β) (r s : ℕ) (b : M.obj w.obj),
    weightedContentUnitClosureValue D Sc cutoff N i M β hh w r s b =
      M.map (X := w.obj) (Y := w.obj)
        (weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s) b

private def CapEvaluation (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : Prop :=
  ∀ (hh : contentCrossingHeight D cutoff i β ≤ 0) (r s : ℕ) (b : M.obj w.obj),
    weightedContentCapClosureValue D Sc cutoff N i M β hh w r s b =
      M.map (X := w.obj) (Y := w.obj)
        (weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s) b

private theorem unit_atWord_evaluate (l : List I) :
    UnitEvaluation D Sc cutoff N i M (l : Multiset I)
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ := by
  intro hh r s b
  exact (unit_atWord_raw D Sc cutoff N i M l hh r s b).trans
    (congrArg (fun f : (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ ⟶
      (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ =>
        M.map (X := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
          (Y := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩) f b)
      (unitCoefficient_atWord D Sc cutoff N i l hh r s).symm)

private theorem cap_atWord_evaluate (l : List I) :
    CapEvaluation D Sc cutoff N i M (l : Multiset I)
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ := by
  intro hh r s b
  exact (cap_atWord_raw D Sc cutoff N i M l hh r s b).trans
    (congrArg (fun f : (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ ⟶
      (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ =>
        M.map (X := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
          (Y := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩) f b)
      (capCoefficient_atWord D Sc cutoff N i l hh r s).symm)

/-- The specified unit closure is the action of its original represented coefficient. -/
theorem weightedContentUnitClosureValue_evaluate (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) (b : M.obj w.obj) :
    weightedContentUnitClosureValue D Sc cutoff N i M β hh w r s b =
    M.map (X := w.obj) (Y := w.obj)
      (weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s) b :=
  (contentRec D Sc cutoff N (P := UnitEvaluation D Sc cutoff N i M)
    (unit_atWord_evaluate D Sc cutoff N i M) β w) hh r s b

/-- The specified cap closure retains the same represented coefficient at arbitrary content. -/
theorem weightedContentCapClosureValue_evaluate (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) (b : M.obj w.obj) :
    weightedContentCapClosureValue D Sc cutoff N i M β hh w r s b =
    M.map (X := w.obj) (Y := w.obj)
      (weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s) b :=
  (contentRec D Sc cutoff N (P := CapEvaluation D Sc cutoff N i M)
    (cap_atWord_evaluate D Sc cutoff N i M) β w) hh r s b

private theorem unitWordCoefficient_degree (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (l : List I) (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I)) (r s : ℕ) :
    unitWordCoefficient D Sc cutoff N i l hh r s ∈
      truncatedDegree D Sc cutoff sy hc N l l (2 * sy.d i * (r + s + 1 : ℕ)) := by
  unfold unitWordCoefficient
  change truncateOld D Sc cutoff N l l _ ∈ _
  apply truncateOld_mem_degree
  have h := positiveKernelClosure_degree D Sc cutoff sy hc i
    (⟨l⟩ : OldCategory D Sc cutoff) ⟨l⟩ hh r s
    ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree ⟨l⟩)
  simpa only [zero_add] using h

private theorem capWordCoefficient_degree (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (l : List I) (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0) (r s : ℕ) :
    capWordCoefficient D Sc cutoff N i l hh r s ∈
      truncatedDegree D Sc cutoff sy hc N l l (2 * sy.d i * (r + s + 1 : ℕ)) := by
  unfold capWordCoefficient
  change truncateOld D Sc cutoff N l l _ ∈ _
  apply truncateOld_mem_degree
  have h := negativeKernelClosure_degree D Sc cutoff sy hc i
    (⟨l⟩ : OldCategory D Sc cutoff) ⟨l⟩ hh r s
    ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree ⟨l⟩)
  simpa only [zero_add] using h

private def UnitCoefficientDegree (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : Prop :=
  ∀ (hh : 0 ≤ contentCrossingHeight D cutoff i β) (r s : ℕ),
    weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word (2 * sy.d i * (r + s + 1 : ℕ))

private def CapCoefficientDegree (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : Prop :=
  ∀ (hh : contentCrossingHeight D cutoff i β ≤ 0) (r s : ℕ),
    weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word (2 * sy.d i * (r + s + 1 : ℕ))

/-- The represented unit coefficient has the positive source integer degree. -/
theorem weightedContentUnitClosureCoefficient_degree
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (w : ContentCategory D Sc cutoff N β) (r s : ℕ) :
    weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word (2 * sy.d i * (r + s + 1 : ℕ)) := by
  have h : UnitCoefficientDegree D Sc cutoff N i sy hc β w :=
    contentRec D Sc cutoff N (P := UnitCoefficientDegree D Sc cutoff N i sy hc)
      (fun l hh r s => (unitCoefficient_atWord D Sc cutoff N i l hh r s).symm ▸
        unitWordCoefficient_degree D Sc cutoff N i sy hc l hh r s) β w
  exact h hh r s

/-- The represented cap coefficient has the same positive source integer degree. -/
theorem weightedContentCapClosureCoefficient_degree
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) (hh : contentCrossingHeight D cutoff i β ≤ 0)
    (w : ContentCategory D Sc cutoff N β) (r s : ℕ) :
    weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word (2 * sy.d i * (r + s + 1 : ℕ)) := by
  have h : CapCoefficientDegree D Sc cutoff N i sy hc β w :=
    contentRec D Sc cutoff N (P := CapCoefficientDegree D Sc cutoff N i sy hc)
      (fun l hh r s => (capCoefficient_atWord D Sc cutoff N i l hh r s).symm ▸
        capWordCoefficient_degree D Sc cutoff N i sy hc l hh r s) β w
  exact h hh r s

/-- Properties of the represented unit coefficient are checked on the truncated raw closure at
each stored word. -/
theorem weightedContentUnitClosureCoefficient_induction
    {P : ∀ (β : Multiset I) (w : ContentCategory D Sc cutoff N β), ℕ → ℕ → (w.obj ⟶ w.obj) → Prop}
    (h : ∀ (l : List I) (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I)) (r s : ℕ),
      P (l : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s
        (truncateOld D Sc cutoff N l l
          (positiveKernelClosure D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _))))
    (β : Multiset I) (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (w : ContentCategory D Sc cutoff N β) (r s : ℕ) :
    P β w r s (weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s) := by
  have hw : ∀ (hh : 0 ≤ contentCrossingHeight D cutoff i β) (r s : ℕ),
      P β w r s (weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s) :=
    contentRec D Sc cutoff N
      (P := fun β w => ∀ (hh : 0 ≤ contentCrossingHeight D cutoff i β) (r s : ℕ),
        P β w r s (weightedContentUnitClosureCoefficient D Sc cutoff N i β hh w r s))
      (fun l hh r s => by
        rw [unitCoefficient_atWord D Sc cutoff N i l hh r s]
        unfold unitWordCoefficient
        exact h l hh r s) β w
  exact hw hh r s

/-- Properties of the represented cap coefficient are checked on the truncated raw closure at
each stored word. -/
theorem weightedContentCapClosureCoefficient_induction
    {P : ∀ (β : Multiset I) (w : ContentCategory D Sc cutoff N β), ℕ → ℕ → (w.obj ⟶ w.obj) → Prop}
    (h : ∀ (l : List I) (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0) (r s : ℕ),
      P (l : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s
        (truncateOld D Sc cutoff N l l
          (negativeKernelClosure D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _))))
    (β : Multiset I) (hh : contentCrossingHeight D cutoff i β ≤ 0)
    (w : ContentCategory D Sc cutoff N β) (r s : ℕ) :
    P β w r s (weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s) := by
  have hw : ∀ (hh : contentCrossingHeight D cutoff i β ≤ 0) (r s : ℕ),
      P β w r s (weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s) :=
    contentRec D Sc cutoff N
      (P := fun β w => ∀ (hh : contentCrossingHeight D cutoff i β ≤ 0) (r s : ℕ),
        P β w r s (weightedContentCapClosureCoefficient D Sc cutoff N i β hh w r s))
      (fun l hh r s => by
        rw [capCoefficient_atWord D Sc cutoff N i l hh r s]
        unfold capWordCoefficient
        exact h l hh r s) β w
  exact hw hh r s

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Window entries of the specified weighted local inverses

BE (1.13)–(1.14): evaluation retains every finite projection or insertion
of the same finite content matrix inverse, with its named parity isomorphism.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction OddMath.FiniteSupermodule CyclotomicCrossingTensor
  CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) (β : Multiset I)
local instance weightedWindowPi : PiSupercategory k
    (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) := supermodulePiSupercategory
local instance weightedWindowOldPi : PiSupercategory k
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) := supermodulePiSupercategory
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "R" => restriction (contentInclusion D Sc cutoff N β)

/-- The unit local window is the actual inverse's literal `some j` row. -/
theorem weightedContentLocalInverseFrom_window_total
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (j : Fin (contentUnitCount D cutoff i β))
    (z : ((restriction (T)).obj (induced (T) M)).obj w.obj) :
    ((weightedContentLocalInverseFrom D Sc cutoff N i M β hh).g' j.val).total w z =
      (((SKM.homParityShiftDatum (k := k) (j.val • D.parity i)).iso M).hom.total w.obj)
        (((weightedContentUnitMatrixIso D Sc cutoff N i M β hh).inv.total w z) (some j)) := by
  classical
  dsimp only [weightedContentLocalInverseFrom, localInverseFromColumns,
    inverseUnitSlot]
  simp only [j.isLt, dite_true]
  dsimp only [inverseCoordinateRow, optionRestoringIso]
  simp only [Iso.trans_inv, eqToIso.inv]
  dsimp only [restriction_finiteProduct]
  simp only [eqToHom_refl, Category.comp_id, Superfunctor.comp_total]
  change (((R).mapIso ((SKM.homParityShiftDatum (k := k) (j.val • D.parity i)).iso M)).hom.total w)
      ((projectionHom (fun a => (R).obj (weightedUnitMatrixFamily D Sc cutoff N i M
        (contentUnitCount D cutoff i β) a)) (some j)).total w
        ((weightedContentUnitMatrixIso D Sc cutoff N i M β hh).inv.total w z)) = _
  rw [projectionHom_total_apply]
  rfl

/-- The cap local window is the actual inverse's literal `some j` column. -/
theorem weightedContentLocalInverseTo_window_total
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (j : Fin (contentCapCount D cutoff i β)) (z : M.obj w.obj) :
    ((weightedContentLocalInverseTo D Sc cutoff N i M β hh).g' j.val).total w z =
      (weightedContentCapMatrixIso D Sc cutoff N i M β hh).inv.total w
        (Pi.single (some j)
          ((((SKM.homParityShiftDatum (k := k) (j.val • D.parity i)).iso M).inv.total w.obj) z)) := by
  classical
  dsimp only [weightedContentLocalInverseTo, localInverseToRows,
    inverseCapSlot]
  simp only [j.isLt, dite_true]
  dsimp only [inverseCoordinateColumn, optionRestoringIso]
  simp only [Iso.trans_inv, eqToIso.inv]
  dsimp only [restriction_finiteProduct]
  simp only [eqToHom_refl, Category.id_comp, Superfunctor.comp_total]
  change (weightedContentCapMatrixIso D Sc cutoff N i M β hh).inv.total w
    ((inclusionHom (fun a => (R).obj (weightedCapMatrixFamily D Sc cutoff N i M
        (contentCapCount D cutoff i β) a)) (some j)).total w
      ((((R).mapIso ((SKM.homParityShiftDatum (k := k) (j.val • D.parity i)).iso M)).inv.total w) z)) = _
  congr 1
  apply funext
  intro a
  by_cases ha : a = some j
  · subst a
    simp only [inclusionHom_total_self, Pi.single_eq_same]
    rfl
  · rw [inclusionHom_total_ne _ (some j) a (Ne.symm ha)]
    symm
    apply Pi.single_eq_of_ne
    exact ha

local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "RM" => weightedRestriction D Sc cutoff N M

private theorem moduleIso_apply_2 {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) (x : F.obj w) :
    moduleIsoLinearEquiv e w x = e.hom.total w x := rfl
private theorem moduleIso_symm_apply_2 {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (e : F ≅ G) (w : C) (x : G.obj w) :
    (moduleIsoLinearEquiv e w).symm x = e.inv.total w x := rfl

/-- Every finite weighted inverse row is retained by the full matrix chart. -/
theorem weightedUnitInverse_window (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (j : Fin (contentUnitCount D cutoff i (w.word : Multiset I)))
    (z : mateTargetSpace D Sc cutoff i RM w) :
    weightedUnitFamilyValueEquiv D Sc cutoff N i M _ w (some j)
      (((moduleUnitMatrixIso D Sc cutoff RM i w hh).inv z) (some j)) =
    ((weightedUnitMatrixComponentIso D Sc cutoff N i M w hh).inv
      (weightedMateTargetLinearEquiv D Sc cutoff N i M w z)) (some j) :=
  congrFun (weightedUnitInverse_coordinates D Sc cutoff N i M w hh z) (some j)

/-- Every finite unit `g'` retains the OLD inverse row in the selected chart. -/
theorem weightedContentUnitWindow_chart (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (j : Fin (contentUnitCount D cutoff i (w.word : Multiset I)))
    (z : mateTargetSpace D Sc cutoff i RM w) :
    ((weightedContentLocalInverseFrom D Sc cutoff N i M (w.word : Multiset I) hh).g' j.val).total
      (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I))
      (weightedMateTargetLinearEquiv D Sc cutoff N i M w z) =
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
      (j.val • D.parity i)).iso RM) w
      (((moduleUnitMatrixIso D Sc cutoff RM i w hh).inv z) (some j)) := by
  have h₀ := weightedContentLocalInverseFrom_window_total D Sc cutoff N i M
    (w.word : Multiset I) hh
    (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I)) j
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w z)
  rw [weightedContentUnitInverse_atWord D Sc cutoff N i M w hh] at h₀
  have h₁ := shiftedModuleValueLinearEquiv_hom_coordinate RM M w ((Q).obj w)
    (LinearEquiv.refl k _) (j.val • D.parity i)
    (((moduleUnitMatrixIso D Sc cutoff RM i w hh).inv z) (some j))
  have h₂ := congrArg
    (((SKM.homParityShiftDatum (k := k) (j.val • D.parity i)).iso M).hom.total ((Q).obj w))
    (weightedUnitInverse_window D Sc cutoff N i M w hh j z)
  dsimp only [weightedUnitFamilyValueEquiv] at h₂
  simp only [moduleIso_apply_2]
  exact h₀.trans (h₂.symm.trans h₁)

/-- Every finite cap target insertion retains its prescribed parity chart. -/
theorem weightedCapWindowInput_coordinates (w : OldCategory D Sc cutoff)
    (m : ℕ) (j : Fin m) (z : (RM).obj w) :
    weightedCapMatrixValueEquiv D Sc cutoff N i M m w
      (Pi.single (some j)
        ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
          (j.val • D.parity i)).iso RM) w).symm z)) =
    Pi.single (some j)
      ((((SKM.homParityShiftDatum (k := k) (j.val • D.parity i)).iso M).inv.total ((Q).obj w)) z) := by
  classical
  funext a
  change weightedCapFamilyValueEquiv D Sc cutoff N i M m w a
    ((Pi.single (some j)
      ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
        (j.val • D.parity i)).iso RM) w).symm z) :
      ∀ a, (capMatrixFamily D Sc cutoff i RM m a).obj w) a) = _
  by_cases ha : a = some j
  · subst a
    simp only [Pi.single_eq_same, moduleIso_symm_apply_2]
    dsimp only [weightedCapFamilyValueEquiv]
    exact shiftedModuleValueLinearEquiv_inv_coordinate RM M w ((Q).obj w)
      (LinearEquiv.refl k _) (j.val • D.parity i) z
  · simp only [Pi.single_eq_of_ne ha, map_zero]

/-- Every finite cap `g'` retains the OLD inverse column in the selected chart. -/
theorem weightedContentCapWindow_chart (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0)
    (j : Fin (contentCapCount D cutoff i (w.word : Multiset I))) (z : (RM).obj w) :
    ((weightedContentLocalInverseTo D Sc cutoff N i M (w.word : Multiset I) hh).g' j.val).total
      (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I)) z =
    weightedMateSourceLinearEquiv D Sc cutoff N i M w
      ((moduleCapMatrixIso D Sc cutoff RM i w hh).inv
        (Pi.single (some j)
          ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
            (j.val • D.parity i)).iso RM) w).symm z))) := by
  have h₀ := weightedContentLocalInverseTo_window_total D Sc cutoff N i M
    (w.word : Multiset I) hh
    (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I)) j z
  rw [weightedContentCapInverse_atWord D Sc cutoff N i M w hh] at h₀
  have h₁ := congrArg (weightedCapMatrixComponentIso D Sc cutoff N i M w hh).inv
    (weightedCapWindowInput_coordinates D Sc cutoff N i M w
      (contentCapCount D cutoff i (w.word : Multiset I)) j z)
  have h₂ := weightedCapInverse_coordinates D Sc cutoff N i M w hh
    (Pi.single (some j)
      ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
        (j.val • D.parity i)).iso RM) w).symm z))
  exact h₀.trans (h₁.symm.trans h₂.symm)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Weighted boundary contractions in raw kernel coordinates

SwappedHomInversion §4 (7): evaluate the chosen weighted finite `g'`
contractions by the raw OLD boundary coefficients in both height orientations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local instance boundaryWeightedPi : PiSupercategory k
    (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) := supermodulePiSupercategory
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The prescribed weighted unit followed by its finite inverse row. -/
def weightedContentUnitBoundaryValue (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (j : Fin (contentUnitCount D cutoff i β)) (r : ℕ) (b : M.obj w.obj) :=
  ((weightedContentLocalInverseFrom D Sc cutoff N i M β hh).g' j.val).total w
    ((unitDotColumn (T) (truncatedDot_supernatural D Sc cutoff N i) M r).total w.obj b)

/-- The prescribed finite cap inverse column followed by an ordinary cap row. -/
def weightedContentCapBoundaryValue (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (r : ℕ) (j : Fin (contentCapCount D cutoff i β)) (b : M.obj w.obj) :=
  (capDotRow (T) (truncatedDot_supernatural D Sc cutoff N i) M r).total w.obj
    (((weightedContentLocalInverseTo D Sc cutoff N i M β hh).g' j.val).total w b)

/-- Evaluation of the specified weighted unit boundary is the raw represented boundary. -/
theorem weightedContentUnitBoundaryValue_atWord (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (j : Fin (contentUnitCount D cutoff i (w.word : Multiset I))) (r : ℕ) (b : (RM).obj w) :
    weightedContentUnitBoundaryValue D Sc cutoff N i M (w.word : Multiset I) hh
      (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I)) j r b =
    (RM).map (positiveKernelBoundary D Sc cutoff i w w hh j r (𝟙 w)) b := by
  unfold weightedContentUnitBoundaryValue
  rw [← weightedUnitColumnValue_compare D Sc cutoff N i M w r b]
  rw [weightedContentUnitWindow_chart D Sc cutoff N i M w hh]
  have h := positiveKernelBoundary_evaluate D Sc cutoff RM i w w hh j r (𝟙 w) b
  have hi : (RM).map (𝟙 w) b = b :=
    congrArg (fun f : (RM).obj w ⟶ (RM).obj w => f b) ((RM).toFunctor.map_id w)
  rw [hi] at h
  exact h.symm

/-- Evaluation of the specified weighted cap boundary is the raw represented boundary. -/
theorem weightedContentCapBoundaryValue_atWord (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0)
    (r : ℕ) (j : Fin (contentCapCount D cutoff i (w.word : Multiset I))) (b : (RM).obj w) :
    weightedContentCapBoundaryValue D Sc cutoff N i M (w.word : Multiset I) hh
      (⟨(Q).obj w,rfl⟩ : ContentCategory D Sc cutoff N (w.word : Multiset I)) r j b =
    (RM).map (negativeKernelBoundary D Sc cutoff i w w hh r j (𝟙 w)) b := by
  unfold weightedContentCapBoundaryValue
  rw [weightedContentCapWindow_chart D Sc cutoff N i M w hh]
  rw [← weightedCapRowValue_compare D Sc cutoff N i M w r]
  have h := negativeKernelBoundary_evaluate D Sc cutoff RM i w w hh r j (𝟙 w) b
  have hi : (RM).map (𝟙 w) b = b :=
    congrArg (fun f : (RM).obj w ⟶ (RM).obj w => f b) ((RM).toFunctor.map_id w)
  rw [hi] at h
  exact h.symm

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Weighted kernel boundary coefficients at arbitrary stored content

SwappedHomInversion §4 (7): the literal chosen weighted finite inverse
contractions act by their original source coefficients, with difference
degree, for arbitrary formal content and every finite window slot.
-/
noncomputable section
set_option backward.dsimp.instances true
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u v
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

attribute [local irreducible] positiveKernelBoundary negativeKernelBoundary
  weightedContentUnitBoundaryValue weightedContentCapBoundaryValue

private def contentRec_2
    {P : ∀ β : Multiset I, ContentCategory D Sc cutoff N β → Sort v}
    (h : ∀ l : List I,
      P (l : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩)
    (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : P β w := by
  rcases w with ⟨t, ht⟩
  cases ht
  exact h t.word

private theorem contentRec_atWord_2
    {P : ∀ β : Multiset I, ContentCategory D Sc cutoff N β → Sort v}
    (h : ∀ l : List I,
      P (l : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩)
    (l : List I) :
    contentRec_2 D Sc cutoff N h (l : Multiset I)
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ = h l := rfl

private def unitWordCoefficient_2 (l : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I)) (r : Fin (contentUnitCount D cutoff i (l : Multiset I))) (s : ℕ) :
    (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ ⟶
      (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ :=
  truncateOld D Sc cutoff N l l
    (positiveKernelBoundary D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _))

private def capWordCoefficient_2 (l : List I)
    (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0) (r : ℕ) (s : Fin (contentCapCount D cutoff i (l : Multiset I))) :
    (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ ⟶
      (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ :=
  truncateOld D Sc cutoff N l l
    (negativeKernelBoundary D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _))

/-- The represented source endomorphism for the prescribed unit boundary. -/
def weightedContentUnitBoundaryCoefficient (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (r : Fin (contentUnitCount D cutoff i β)) (s : ℕ) : w.obj ⟶ w.obj :=
  contentRec_2 D Sc cutoff N
    (P := fun β w => (0 ≤ contentCrossingHeight D cutoff i β) → Fin (contentUnitCount D cutoff i β) → ℕ → (w.obj ⟶ w.obj))
    (unitWordCoefficient_2 D Sc cutoff N i) β w hh r s

/-- The represented source endomorphism for the prescribed cap boundary. -/
def weightedContentCapBoundaryCoefficient (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (r : ℕ) (s : Fin (contentCapCount D cutoff i β)) : w.obj ⟶ w.obj :=
  contentRec_2 D Sc cutoff N
    (P := fun β w => (contentCrossingHeight D cutoff i β ≤ 0) → ℕ → Fin (contentCapCount D cutoff i β) → (w.obj ⟶ w.obj))
    (capWordCoefficient_2 D Sc cutoff N i) β w hh r s

private theorem unitCoefficient_atWord_2 (l : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I)) (r : Fin (contentUnitCount D cutoff i (l : Multiset I))) (s : ℕ) :
    weightedContentUnitBoundaryCoefficient D Sc cutoff N i (l : Multiset I) hh
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s =
    unitWordCoefficient_2 D Sc cutoff N i l hh r s := by
  exact congrFun (congrFun (congrFun
    (contentRec_atWord_2 D Sc cutoff N
      (P := fun β w => (0 ≤ contentCrossingHeight D cutoff i β) → Fin (contentUnitCount D cutoff i β) → ℕ → (w.obj ⟶ w.obj))
      (unitWordCoefficient_2 D Sc cutoff N i) l) hh) r) s

private theorem capCoefficient_atWord_2 (l : List I)
    (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0) (r : ℕ) (s : Fin (contentCapCount D cutoff i (l : Multiset I))) :
    weightedContentCapBoundaryCoefficient D Sc cutoff N i (l : Multiset I) hh
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s =
    capWordCoefficient_2 D Sc cutoff N i l hh r s := by
  exact congrFun (congrFun (congrFun
    (contentRec_atWord_2 D Sc cutoff N
      (P := fun β w => (contentCrossingHeight D cutoff i β ≤ 0) → ℕ → Fin (contentCapCount D cutoff i β) → (w.obj ⟶ w.obj))
      (capWordCoefficient_2 D Sc cutoff N i) l) hh) r) s

private theorem restriction_map_value_2 (t w : OldCategory D Sc cutoff) (f : t ⟶ w)
    (b : (RM).obj t) :
    (RM).map f b = M.map (X := (oldTruncateFunctor D Sc cutoff N).obj t)
      (Y := (oldTruncateFunctor D Sc cutoff N).obj w)
      ((oldTruncateFunctor D Sc cutoff N).map f) b := rfl
private theorem quotient_map_value_2 (t w : OldCategory D Sc cutoff) (f : t ⟶ w) :
    (oldTruncateFunctor D Sc cutoff N).map f =
      truncateOld D Sc cutoff N t.word w.word f := rfl

private theorem restriction_truncate_value_2 (t w : OldCategory D Sc cutoff) (f : t ⟶ w)
    (b : (RM).obj t) :
    (RM).map f b = M.map (X := (oldTruncateFunctor D Sc cutoff N).obj t)
      (Y := (oldTruncateFunctor D Sc cutoff N).obj w)
      (truncateOld D Sc cutoff N t.word w.word f) b := by
  exact (restriction_map_value_2 D Sc cutoff N M t w f b).trans
    (congrArg (fun a : (oldTruncateFunctor D Sc cutoff N).obj t ⟶
      (oldTruncateFunctor D Sc cutoff N).obj w =>
        M.map (X := (oldTruncateFunctor D Sc cutoff N).obj t)
          (Y := (oldTruncateFunctor D Sc cutoff N).obj w) a b)
      (quotient_map_value_2 D Sc cutoff N t w f))

private theorem unit_atWord_raw_2 (l : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (l : Multiset I))) (s : ℕ) (b : (RM).obj ⟨l⟩) :
    weightedContentUnitBoundaryValue D Sc cutoff N i M (l : Multiset I) hh
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s b =
    M.map (X := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
      (Y := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
      (unitWordCoefficient_2 D Sc cutoff N i l hh r s) b := by
  exact (weightedContentUnitBoundaryValue_atWord D Sc cutoff N i M ⟨l⟩ hh r s b).trans
    (restriction_truncate_value_2 D Sc cutoff N M ⟨l⟩ ⟨l⟩
      (positiveKernelBoundary D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _)) b)

private theorem cap_atWord_raw_2 (l : List I)
    (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0)
    (r : ℕ) (s : Fin (contentCapCount D cutoff i (l : Multiset I))) (b : (RM).obj ⟨l⟩) :
    weightedContentCapBoundaryValue D Sc cutoff N i M (l : Multiset I) hh
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s b =
    M.map (X := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
      (Y := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
      (capWordCoefficient_2 D Sc cutoff N i l hh r s) b := by
  exact (weightedContentCapBoundaryValue_atWord D Sc cutoff N i M ⟨l⟩ hh r s b).trans
    (restriction_truncate_value_2 D Sc cutoff N M ⟨l⟩ ⟨l⟩
      (negativeKernelBoundary D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _)) b)

attribute [local irreducible] unitWordCoefficient_2 capWordCoefficient_2
  weightedContentUnitBoundaryCoefficient weightedContentCapBoundaryCoefficient

private def UnitEvaluation_2 (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : Prop :=
  ∀ (hh : 0 ≤ contentCrossingHeight D cutoff i β) (r : Fin (contentUnitCount D cutoff i β)) (s : ℕ) (b : M.obj w.obj),
    weightedContentUnitBoundaryValue D Sc cutoff N i M β hh w r s b =
      M.map (X := w.obj) (Y := w.obj)
        (weightedContentUnitBoundaryCoefficient D Sc cutoff N i β hh w r s) b

private def CapEvaluation_2 (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : Prop :=
  ∀ (hh : contentCrossingHeight D cutoff i β ≤ 0) (r : ℕ) (s : Fin (contentCapCount D cutoff i β)) (b : M.obj w.obj),
    weightedContentCapBoundaryValue D Sc cutoff N i M β hh w r s b =
      M.map (X := w.obj) (Y := w.obj)
        (weightedContentCapBoundaryCoefficient D Sc cutoff N i β hh w r s) b

private theorem unit_atWord_evaluate_2 (l : List I) :
    UnitEvaluation_2 D Sc cutoff N i M (l : Multiset I)
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ := by
  intro hh r s b
  exact (unit_atWord_raw_2 D Sc cutoff N i M l hh r s b).trans
    (congrArg (fun f : (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ ⟶
      (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ =>
        M.map (X := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
          (Y := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩) f b)
      (unitCoefficient_atWord_2 D Sc cutoff N i l hh r s).symm)

private theorem cap_atWord_evaluate_2 (l : List I) :
    CapEvaluation_2 D Sc cutoff N i M (l : Multiset I)
      ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ := by
  intro hh r s b
  exact (cap_atWord_raw_2 D Sc cutoff N i M l hh r s b).trans
    (congrArg (fun f : (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ ⟶
      (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩ =>
        M.map (X := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩)
          (Y := (oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩) f b)
      (capCoefficient_atWord_2 D Sc cutoff N i l hh r s).symm)

/-- The specified unit boundary is the action of its original represented coefficient. -/
theorem weightedContentUnitBoundaryValue_evaluate (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (r : Fin (contentUnitCount D cutoff i β)) (s : ℕ) (b : M.obj w.obj) :
    weightedContentUnitBoundaryValue D Sc cutoff N i M β hh w r s b =
    M.map (X := w.obj) (Y := w.obj)
      (weightedContentUnitBoundaryCoefficient D Sc cutoff N i β hh w r s) b :=
  (contentRec_2 D Sc cutoff N (P := UnitEvaluation_2 D Sc cutoff N i M)
    (unit_atWord_evaluate_2 D Sc cutoff N i M) β w) hh r s b

/-- The specified cap boundary retains the same represented coefficient at arbitrary content. -/
theorem weightedContentCapBoundaryValue_evaluate (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (r : ℕ) (s : Fin (contentCapCount D cutoff i β)) (b : M.obj w.obj) :
    weightedContentCapBoundaryValue D Sc cutoff N i M β hh w r s b =
    M.map (X := w.obj) (Y := w.obj)
      (weightedContentCapBoundaryCoefficient D Sc cutoff N i β hh w r s) b :=
  (contentRec_2 D Sc cutoff N (P := CapEvaluation_2 D Sc cutoff N i M)
    (cap_atWord_evaluate_2 D Sc cutoff N i M) β w) hh r s b

private theorem unitWordCoefficient_degree_2 (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (l : List I) (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I)) (r : Fin (contentUnitCount D cutoff i (l : Multiset I))) (s : ℕ) :
    unitWordCoefficient_2 D Sc cutoff N i l hh r s ∈
      truncatedDegree D Sc cutoff sy hc N l l (2 * sy.d i * ((s : ℤ) - r.val)) := by
  unfold unitWordCoefficient_2
  change truncateOld D Sc cutoff N l l _ ∈ _
  apply truncateOld_mem_degree
  have h := positiveKernelBoundary_degree D Sc cutoff sy hc i
    (⟨l⟩ : OldCategory D Sc cutoff) ⟨l⟩ hh r s
    ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree ⟨l⟩)
  simpa only [zero_add] using h

private theorem capWordCoefficient_degree_2 (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (l : List I) (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0) (r : ℕ) (s : Fin (contentCapCount D cutoff i (l : Multiset I))) :
    capWordCoefficient_2 D Sc cutoff N i l hh r s ∈
      truncatedDegree D Sc cutoff sy hc N l l (2 * sy.d i * ((r : ℤ) - s.val)) := by
  unfold capWordCoefficient_2
  change truncateOld D Sc cutoff N l l _ ∈ _
  apply truncateOld_mem_degree
  have h := negativeKernelBoundary_degree D Sc cutoff sy hc i
    (⟨l⟩ : OldCategory D Sc cutoff) ⟨l⟩ hh r s
    ((oldCategoryGradedSupercategory D Sc cutoff sy hc).id_mem_degree ⟨l⟩)
  simpa only [zero_add] using h

private def UnitCoefficientDegree_2 (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : Prop :=
  ∀ (hh : 0 ≤ contentCrossingHeight D cutoff i β) (r : Fin (contentUnitCount D cutoff i β)) (s : ℕ),
    weightedContentUnitBoundaryCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word (2 * sy.d i * ((s : ℤ) - r.val))

private def CapCoefficientDegree_2 (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : Prop :=
  ∀ (hh : contentCrossingHeight D cutoff i β ≤ 0) (r : ℕ) (s : Fin (contentCapCount D cutoff i β)),
    weightedContentCapBoundaryCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word (2 * sy.d i * ((r : ℤ) - s.val))

/-- The represented unit coefficient has the positive source integer degree. -/
theorem weightedContentUnitBoundaryCoefficient_degree
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (w : ContentCategory D Sc cutoff N β) (r : Fin (contentUnitCount D cutoff i β)) (s : ℕ) :
    weightedContentUnitBoundaryCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word (2 * sy.d i * ((s : ℤ) - r.val)) := by
  have h : UnitCoefficientDegree_2 D Sc cutoff N i sy hc β w :=
    contentRec_2 D Sc cutoff N (P := UnitCoefficientDegree_2 D Sc cutoff N i sy hc)
      (fun l hh r s => (unitCoefficient_atWord_2 D Sc cutoff N i l hh r s).symm ▸
        unitWordCoefficient_degree_2 D Sc cutoff N i sy hc l hh r s) β w
  exact h hh r s

/-- The represented cap coefficient has the same positive source integer degree. -/
theorem weightedContentCapBoundaryCoefficient_degree
    (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
    (β : Multiset I) (hh : contentCrossingHeight D cutoff i β ≤ 0)
    (w : ContentCategory D Sc cutoff N β) (r : ℕ) (s : Fin (contentCapCount D cutoff i β)) :
    weightedContentCapBoundaryCoefficient D Sc cutoff N i β hh w r s ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word (2 * sy.d i * ((r : ℤ) - s.val)) := by
  have h : CapCoefficientDegree_2 D Sc cutoff N i sy hc β w :=
    contentRec_2 D Sc cutoff N (P := CapCoefficientDegree_2 D Sc cutoff N i sy hc)
      (fun l hh r s => (capCoefficient_atWord_2 D Sc cutoff N i l hh r s).symm ▸
        capWordCoefficient_degree_2 D Sc cutoff N i sy hc l hh r s) β w
  exact h hh r s

/-- Properties of the represented unit boundary coefficient are checked on the truncated raw
boundary at each stored word. -/
theorem weightedContentUnitBoundaryCoefficient_induction
    {P : ∀ (β : Multiset I) (w : ContentCategory D Sc cutoff N β),
      Fin (contentUnitCount D cutoff i β) → ℕ → (w.obj ⟶ w.obj) → Prop}
    (h : ∀ (l : List I) (hh : 0 ≤ contentCrossingHeight D cutoff i (l : Multiset I))
      (r : Fin (contentUnitCount D cutoff i (l : Multiset I))) (s : ℕ),
      P (l : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s
        (truncateOld D Sc cutoff N l l
          (positiveKernelBoundary D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _))))
    (β : Multiset I) (hh : 0 ≤ contentCrossingHeight D cutoff i β)
    (w : ContentCategory D Sc cutoff N β) (r : Fin (contentUnitCount D cutoff i β)) (s : ℕ) :
    P β w r s (weightedContentUnitBoundaryCoefficient D Sc cutoff N i β hh w r s) := by
  have hw : ∀ (hh : 0 ≤ contentCrossingHeight D cutoff i β)
      (r : Fin (contentUnitCount D cutoff i β)) (s : ℕ),
      P β w r s (weightedContentUnitBoundaryCoefficient D Sc cutoff N i β hh w r s) :=
    contentRec_2 D Sc cutoff N
      (P := fun β w => ∀ (hh : 0 ≤ contentCrossingHeight D cutoff i β)
        (r : Fin (contentUnitCount D cutoff i β)) (s : ℕ),
        P β w r s (weightedContentUnitBoundaryCoefficient D Sc cutoff N i β hh w r s))
      (fun l hh r s => by
        rw [unitCoefficient_atWord_2 D Sc cutoff N i l hh r s]
        unfold unitWordCoefficient_2
        exact h l hh r s) β w
  exact hw hh r s

/-- Properties of the represented cap boundary coefficient are checked on the truncated raw
boundary at each stored word. -/
theorem weightedContentCapBoundaryCoefficient_induction
    {P : ∀ (β : Multiset I) (w : ContentCategory D Sc cutoff N β),
      ℕ → Fin (contentCapCount D cutoff i β) → (w.obj ⟶ w.obj) → Prop}
    (h : ∀ (l : List I) (hh : contentCrossingHeight D cutoff i (l : Multiset I) ≤ 0) (r : ℕ)
      (s : Fin (contentCapCount D cutoff i (l : Multiset I))),
      P (l : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj ⟨l⟩, rfl⟩ r s
        (truncateOld D Sc cutoff N l l
          (negativeKernelBoundary D Sc cutoff i ⟨l⟩ ⟨l⟩ hh r s (𝟙 _))))
    (β : Multiset I) (hh : contentCrossingHeight D cutoff i β ≤ 0)
    (w : ContentCategory D Sc cutoff N β) (r : ℕ) (s : Fin (contentCapCount D cutoff i β)) :
    P β w r s (weightedContentCapBoundaryCoefficient D Sc cutoff N i β hh w r s) := by
  have hw : ∀ (hh : contentCrossingHeight D cutoff i β ≤ 0) (r : ℕ)
      (s : Fin (contentCapCount D cutoff i β)),
      P β w r s (weightedContentCapBoundaryCoefficient D Sc cutoff N i β hh w r s) :=
    contentRec_2 D Sc cutoff N
      (P := fun β w => ∀ (hh : contentCrossingHeight D cutoff i β ≤ 0) (r : ℕ)
        (s : Fin (contentCapCount D cutoff i β)),
        P β w r s (weightedContentCapBoundaryCoefficient D Sc cutoff N i β hh w r s))
      (fun l hh r s => by
        rw [capCoefficient_atWord_2 D Sc cutoff N i l hh r s]
        unfold capWordCoefficient_2
        exact h l hh r s) β w
  exact hw hh r s

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Prescribed inverse coefficient rows under weighted descent

The coefficient functional in `SwappedVacuumCoordinates.md`, §6 and
`SwappedVacuumNonpositiveBubbles.md`, §2 must be the prescribed inverse
row in the selected weighted charts. The proved given forward matrix
square determines this inverse comparison, with its original parity unshift.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u

private theorem inverse_chart_square
    {k : Type u} [CommRing k] {V W X Y : SVec k}
    (e : V ≅ W) (f : X ≅ Y) (c : W ≃ₗ[k] Y) (d : V ≃ₗ[k] X)
    (h : c.toLinearMap ∘ₗ SVec.toLinearMap e.hom =
      SVec.toLinearMap f.hom ∘ₗ d.toLinearMap) :
    d.toLinearMap ∘ₗ SVec.toLinearMap e.inv =
      SVec.toLinearMap f.inv ∘ₗ c.toLinearMap := by
  have he (z : W) : e.hom (e.inv z) = z := by
    have hi := congrArg (fun g : W ⟶ W => g z) e.inv_hom_id
    simpa only [SVec.comp_apply, SVec.id_apply] using hi
  have hf (z : X) : f.inv (f.hom z) = z := by
    have hi := congrArg (fun g : X ⟶ X => g z) f.hom_inv_id
    simpa only [SVec.comp_apply, SVec.id_apply] using hi
  apply LinearMap.ext
  intro z
  calc
    d (e.inv z) = f.inv (f.hom (d (e.inv z))) := (hf _).symm
    _ = f.inv (c (e.hom (e.inv z))) := congrArg f.inv (LinearMap.congr_fun h (e.inv z)).symm
    _ = f.inv (c z) := congrArg (fun b => f.inv (c b)) (he z)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]
local instance weightedCoefficientRowsPi :
    PiSupercategory k (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :=
  supermodulePiSupercategory
variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The inverse of the given weighted unit matrix is the inverse of the
given old matrix under the same selected whole finite-family charts. -/
theorem weightedUnitMatrix_inverse_compare (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I)) :
    (weightedUnitMatrixValueEquiv D Sc cutoff N i M
      (contentUnitCount D cutoff i (w.word : Multiset I)) w).toLinearMap ∘ₗ
      SVec.toLinearMap (moduleUnitMatrixIso D Sc cutoff RM i w hh).inv =
    SVec.toLinearMap (weightedUnitMatrixComponentIso D Sc cutoff N i M w hh).inv ∘ₗ
      (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap := by
  apply inverse_chart_square
  rw [moduleUnitMatrixIso_hom, weightedUnitMatrixComponentIso_hom]
  exact weightedMatrixCharts_unitMatrix D Sc cutoff N i M _ w

/-- The original inverse-row parity coordinate, removed after the actual
prescribed weighted inverse. This is not an independently chosen extractor. -/
def weightedUnitCoefficient (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (w.word : Multiset I))) :
    (((restriction T).obj ((induction T).obj M)).obj ((Q).obj w)) →ₗ[k] M.obj ((Q).obj w) :=
  (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
    (r.val • D.parity i)).iso M) ((Q).obj w)).toLinearMap ∘ₗ
      LinearMap.proj (some r) ∘ₗ
        SVec.toLinearMap (weightedUnitMatrixComponentIso D Sc cutoff N i M w hh).inv

/-- The chosen weighted inverse coefficient is exactly the old inverse
coefficient under the selected append chart, with no added scalar. -/
theorem weightedUnitCoefficient_compare (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (w.word : Multiset I))) :
    weightedUnitCoefficient D Sc cutoff N i M w hh r ∘ₗ
      (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap =
    moduleUnitCoefficient D Sc cutoff RM i w hh r := by
  have hi := weightedUnitMatrix_inverse_compare D Sc cutoff N i M w hh
  apply LinearMap.ext
  intro z
  have hz := congrFun (LinearMap.congr_fun hi z) (some r)
  have hc := congrArg
    (fun b => ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom.total ((Q).obj w) b) hz
  have hu := shiftedModuleValueLinearEquiv_hom_coordinate RM M w ((Q).obj w)
    (LinearEquiv.refl k _) (r.val • D.parity i)
    (((moduleUnitMatrixIso D Sc cutoff RM i w hh).inv z) (some r))
  exact hc.symm.trans hu

/-- The actual weighted inverse coefficient extracts the given weighted
unit/dot columns on every input module vector throughout the finite window. -/
theorem weightedUnitCoefficient_unitDotColumn (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (w.word : Multiset I)))
    (a : ℕ) (ha : a < contentUnitCount D cutoff i (w.word : Multiset I))
    (b : M.obj ((Q).obj w)) :
    weightedUnitCoefficient D Sc cutoff N i M w hh r
      ((unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) M a).total ((Q).obj w) b) =
      if a = r.val then b else 0 := by
  have hc := LinearMap.congr_fun (weightedUnitCoefficient_compare D Sc cutoff N i M w hh r)
    ((moduleUnitColumn D Sc cutoff i RM a).total w b)
  have hu := weightedUnitColumnValue_compare D Sc cutoff N i M w a b
  change weightedUnitCoefficient D Sc cutoff N i M w hh r
      (weightedMateTargetLinearEquiv D Sc cutoff N i M w
        ((moduleUnitColumn D Sc cutoff i RM a).total w b)) =
      moduleUnitCoefficient D Sc cutoff RM i w hh r
        ((moduleUnitColumn D Sc cutoff i RM a).total w b) at hc
  rw [hu] at hc
  by_cases har : a = r.val
  · rw [ite_eq_left har, har]
    rw [har] at hc
    exact hc.trans (moduleUnitCoefficient_column D Sc cutoff RM i w hh r b)
  · rw [ite_eq_right har]
    exact hc.trans (moduleUnitCoefficient_column_ne D Sc cutoff RM i w hh r ⟨a, ha⟩
      (fun he => har (congrArg Fin.val he).symm) b)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The literal power-vacuum coefficient cap in the selected weighted chart

`SwappedVacuumCoordinates.md`, §6, keeps the paper's actual coefficient
power quotient. The upper power/weight containment descends that same
module on unchanged carriers. The selected append chart then identifies
its actual weighted inverse row with its original A/T-valued coefficient
functional. No quotient equality or extra inverse is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
private theorem inductionRestrictionIsoChart_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (M P : Superfunctor k C (SVec k)) (e : M ≅ P) (w : C)
    (V : Type u) [AddCommGroup V] [Module k V]
    (c : Obj J P.toFunctor (J.obj w) ≃ₗ[k] V)
    (z : Obj J M.toFunctor (J.obj w)) :
    ((moduleIsoLinearEquiv ((restriction J).mapIso ((induction J).mapIso e)) w).trans c) z =
      c ((((restriction J).map ((induction J).map e.hom)).total w) z) := rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The original vacuum coefficient row is natural against every even
input-module map. The odd-map version retains the full row-degree sign
in `contentUnitCoefficientMap_supernatural`. -/
theorem moduleUnitCoefficient_vacuum_naturality_even
    {M P : Superfunctor k (OldCategory D Sc cutoff) (SVec k)} {f : M ⟶ P}
    (hf : f ∈ parity (R := k) M P 0) (i : I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (([] : List I) : Multiset I)))
    (z : mateTargetSpace D Sc cutoff i M (⟨[]⟩ : OldCategory D Sc cutoff)) :
    moduleUnitCoefficient D Sc cutoff P i ⟨[]⟩ hh r
      ((((restriction (append D Sc cutoff i)).map
        ((induction (append D Sc cutoff i)).map f)).total ⟨[]⟩) z) =
      f.total ⟨[]⟩ (moduleUnitCoefficient D Sc cutoff M i ⟨[]⟩ hh r z) := by
  have h := (contentUnitCoefficientMap_supernatural D Sc cutoff i [] hh r).naturality hf
  rw [mul_zero, sign_zero, one_smul] at h
  have ht := congrArg
    (fun g => g.total (⟨⟨[]⟩, List.Perm.refl _⟩ : OldContentCategory D Sc cutoff [])) h
  rw [Superfunctor.comp_total, Superfunctor.comp_total] at ht
  have hz := LinearMap.congr_fun ht z
  change (contentUnitCoefficientMap D Sc cutoff P i [] hh r).total
      (⟨⟨[]⟩, List.Perm.refl _⟩ : OldContentCategory D Sc cutoff [])
      ((((restriction (append D Sc cutoff i)).map
        ((induction (append D Sc cutoff i)).map f)).total ⟨[]⟩) z) =
    f.total ⟨[]⟩ ((contentUnitCoefficientMap D Sc cutoff M i [] hh r).total
      (⟨⟨[]⟩, List.Perm.refl _⟩ : OldContentCategory D Sc cutoff []) z) at hz
  rw [contentUnitCoefficientMap_vacuum_total, contentUnitCoefficientMap_vacuum_total] at hz
  exact hz

section Descent
variable (N : ℕ) (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
  (hM : KillsWeightedCoefficients D Sc cutoff N M)
local notation "W" => weightedModule D Sc cutoff N M hM
local notation "RM" => weightedRestriction D Sc cutoff N W
local notation "descentIso" => weightedRestrictionModuleIso D Sc cutoff N M hM

private theorem descentComparison_inv_mem :
    (descentIso).inv ∈ parity (R := k) M RM 0 := by
  exact moduleIsoOfEvenNatIso_inv_mem _ _ _ _ _

/-- The selected append chart on the original annihilated old module.
The first comparison is the actual descent/restriction isomorphism, whose
components are identities on the unchanged module values. -/
def weightedDescentMateTargetEquiv (i : I) (w : OldCategory D Sc cutoff) :
    mateTargetSpace D Sc cutoff i M w ≃ₗ[k]
      (((restriction (truncatedAppend D Sc cutoff N [i])).obj
        ((induction (truncatedAppend D Sc cutoff N [i])).obj W)).obj
          ((oldTruncateFunctor D Sc cutoff N).obj w)) :=
  (moduleIsoLinearEquiv
    ((restriction (append D Sc cutoff i)).mapIso
      ((induction (append D Sc cutoff i)).mapIso (descentIso).symm)) w).trans
    (weightedMateTargetLinearEquiv D Sc cutoff N i W w)

/-- The weighted inverse row on the selected actual descent chart equals
the original vacuum inverse row, before choosing a coefficient quotient. -/
theorem weightedDescentVacuumCoefficient_compare (i : I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (([] : List I) : Multiset I)))
    (z : mateTargetSpace D Sc cutoff i M (⟨[]⟩ : OldCategory D Sc cutoff)) :
    (moduleIsoLinearEquiv descentIso (⟨[]⟩ : OldCategory D Sc cutoff))
      (weightedUnitCoefficient D Sc cutoff N i W ⟨[]⟩ hh r
        (weightedDescentMateTargetEquiv D Sc cutoff N M hM i ⟨[]⟩ z)) =
      moduleUnitCoefficient D Sc cutoff M i ⟨[]⟩ hh r z := by
  have hc := weightedUnitCoefficient_compare D Sc cutoff N i W ⟨[]⟩ hh r
  let f : M ⟶ RM := (descentIso).inv
  have hn := moduleUnitCoefficient_vacuum_naturality_even D Sc cutoff
    (descentComparison_inv_mem D Sc cutoff N M hM) i hh r z
  let z' := (((restriction (append D Sc cutoff i)).map
    ((induction (append D Sc cutoff i)).map f)).total (⟨[]⟩ : OldCategory D Sc cutoff)) z
  have hc' := LinearMap.congr_fun hc z'
  dsimp only [z', f] at hc'
  simp only [LinearMap.comp_apply] at hc'
  have hboth := hc'.trans hn
  have hout := congrArg (moduleIsoLinearEquiv descentIso (⟨[]⟩ : OldCategory D Sc cutoff)) hboth
  have hcancel := (moduleIsoLinearEquiv descentIso (⟨[]⟩ : OldCategory D Sc cutoff)).apply_symm_apply
    (moduleUnitCoefficient D Sc cutoff M i ⟨[]⟩ hh r z)
  unfold weightedDescentMateTargetEquiv
  rw [inductionRestrictionIsoChart_apply, Iso.symm_hom]
  exact hout.trans hcancel

end Descent

namespace PowerVacuumCoefficient
variable [Fintype I] (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "M" => coefficientPowerVacuum D Sc cutoff L

private theorem killsWeighted : KillsWeightedCoefficients D Sc cutoff bound M :=
  (coefficientWeightedIdeal_le_annihilator_iff D Sc cutoff bound M).mp
    ((weighted_le_elementaryPowerIdeal D cutoff L).trans
      (coefficientPowerVacuumObject D Sc cutoff L).property)

/-- The actual power-to-weighted comparison functor applied to the literal
regular A/T vacuum; it introduces no replacement coefficient quotient. -/
def weightedVacuum : Superfunctor k (TruncatedCategory D Sc cutoff bound) (SVec k) :=
  (elementaryPowerToWeighted D Sc cutoff L).obj (coefficientPowerVacuumObject D Sc cutoff L)

omit [Fintype I] in
private theorem height (i : I) :
    0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

private def topSlot (i : I) (hN : 0 < cutoff i) :
    Fin (contentUnitCount D cutoff i (([] : List I) : Multiset I)) :=
  ⟨cutoff i - 1, by rw [VacuumCoefficient.count]; omega⟩

/-- The original literal A/T empty coordinate followed by the inverse
identity-component descent comparison. Its target is the actual weighted
vacuum value, so no carrier identification is silently inferred. -/
def weightedEmptyEquiv : CoefficientPowerQuotient (k := k) D cutoff L ≃ₗ[k]
    (weightedVacuum D Sc cutoff L).obj ((oldTruncateFunctor D Sc cutoff bound).obj ⟨[]⟩) :=
  (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).trans
    (moduleIsoLinearEquiv
      (weightedRestrictionModuleIso D Sc cutoff bound M (killsWeighted D Sc cutoff L))
        (⟨[]⟩ : OldCategory D Sc cutoff)).symm

/-- The prescribed selected weighted append chart starts on the unchanged
literal A/T vacuum induction component. -/
def weightedTargetChart (i : I) :
    mateTargetSpace D Sc cutoff i M (⟨[]⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
      (((restriction (truncatedAppend D Sc cutoff bound [i])).obj
        ((induction (truncatedAppend D Sc cutoff bound [i])).obj
          (weightedVacuum D Sc cutoff L))).obj
            ((oldTruncateFunctor D Sc cutoff bound).obj ⟨[]⟩)) :=
  weightedDescentMateTargetEquiv D Sc cutoff bound M (killsWeighted D Sc cutoff L) i ⟨[]⟩

/-- Decode the actual prescribed weighted last inverse row into literal
A/T using the original empty-vacuum coordinate. -/
def weightedFunctional (i : I) (hN : 0 < cutoff i) :
    (((restriction (truncatedAppend D Sc cutoff bound [i])).obj
      ((induction (truncatedAppend D Sc cutoff bound [i])).obj
        (weightedVacuum D Sc cutoff L))).obj
          ((oldTruncateFunctor D Sc cutoff bound).obj ⟨[]⟩)) →ₗ[k]
      CoefficientPowerQuotient (k := k) D cutoff L :=
  (weightedEmptyEquiv D Sc cutoff L).symm.toLinearMap ∘ₗ
    weightedUnitCoefficient D Sc cutoff bound i (weightedVacuum D Sc cutoff L) ⟨[]⟩
      (height D cutoff i) (topSlot D cutoff i hN)

/-- The original literal-power-vacuum λ is the selected weighted inverse
cap, with exactly the given row, source unshift and empty coordinate. -/
theorem weightedFunctional_compare (i : I) (hN : 0 < cutoff i)
    (z : mateTargetSpace D Sc cutoff i M (⟨[]⟩ : OldCategory D Sc cutoff)) :
    weightedFunctional D Sc cutoff L i hN (weightedTargetChart D Sc cutoff L i z) =
      functional D Sc cutoff L i hN z := by
  have hc := weightedDescentVacuumCoefficient_compare D Sc cutoff bound M
    (killsWeighted D Sc cutoff L) i (height D cutoff i) (topSlot D cutoff i hN) z
  exact congrArg (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).symm hc

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELVOld
end

end
