import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedContentMatrixInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInverseKernelCoordinates

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

/-- At arbitrary content, the only reindexing is the object's proven content
identity; no inverse comparison is an input. -/
theorem weightedContentUnitInverse_component (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β) :
    HEq ((weightedContentUnitMatrixIso D Sc cutoff N i M β hh).inv.total w)
      ((weightedUnitMatrixComponentIso D Sc cutoff N i M ⟨w.obj.word⟩
        (by rw [w.content]; exact hh)).inv) := by
  rcases w with ⟨⟨l⟩,hl⟩
  subst β
  exact heq_of_eq (weightedContentUnitInverse_atWord D Sc cutoff N i M ⟨l⟩ hh)

theorem weightedContentCapInverse_component (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β) :
    HEq ((weightedContentCapMatrixIso D Sc cutoff N i M β hh).inv.total w)
      ((weightedCapMatrixComponentIso D Sc cutoff N i M ⟨w.obj.word⟩
        (by rw [w.content]; exact hh)).inv) := by
  rcases w with ⟨⟨l⟩,hl⟩
  subst β
  exact heq_of_eq (weightedContentCapInverse_atWord D Sc cutoff N i M ⟨l⟩ hh)

/-- The literal weighted principal after removing its named value and parity
charts. This is a coordinate description, with no new choice of inverse. -/
def weightedUnitPrincipalInverseValue (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (z : mateTargetSpace D Sc cutoff i RM w) :=
  moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i RM
    (contentUnitCount D cutoff i (w.word : Multiset I))) w
    ((weightedUnitFamilyValueEquiv D Sc cutoff N i M _ w none).symm
      (((weightedUnitMatrixComponentIso D Sc cutoff N i M w hh).inv
        (weightedMateTargetLinearEquiv D Sc cutoff N i M w z)) none))

/-- This is the principal of the already selected OLD inverse. -/
theorem weightedUnitPrincipalInverseValue_eq (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (z : mateTargetSpace D Sc cutoff i RM w) :
    weightedUnitPrincipalInverseValue D Sc cutoff N i M w hh z =
    moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i RM
      (contentUnitCount D cutoff i (w.word : Multiset I))) w
      (((moduleUnitMatrixIso D Sc cutoff RM i w hh).inv z) none) := by
  unfold weightedUnitPrincipalInverseValue
  apply congrArg (moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i RM
    (contentUnitCount D cutoff i (w.word : Multiset I))) w)
  apply (weightedUnitFamilyValueEquiv D Sc cutoff N i M _ w none).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (weightedUnitInverse_none D Sc cutoff N i M w hh z).symm

/-- The weighted principal inverse applies the raw positive kernel principal
inverse to the coefficient of a pure upper-Hom tensor. -/
theorem weightedUnitPrincipalInverseValue_tensor (w : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (w.word : Multiset I))
    (v : OldCategory D Sc cutoff)
    (y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj w) (b : (RM).obj v) :
    weightedUnitPrincipalInverseValue D Sc cutoff N i M w hh
      (BalancedInduction.tensor (append D Sc cutoff i) (RM).toFunctor v y b) =
    IndResKernel.evaluate (append D Sc cutoff i) (RM).toFunctor v w b
      (positiveKernelPrincipalInverse D Sc cutoff i v w hh y) := by
  rw [weightedUnitPrincipalInverseValue_eq]
  exact moduleUnitMatrixIso_principal_inv_tensor D Sc cutoff RM i w hh v y b

/-- The literal cap inverse after removal of the named source chart. -/
def weightedCapPrincipalInverseValue (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0)
    (z : capMatrixTargetSpace D Sc cutoff i RM
      (contentCapCount D cutoff i (w.word : Multiset I)) w) :=
  (weightedMateSourceLinearEquiv D Sc cutoff N i M w).symm
    ((weightedCapMatrixComponentIso D Sc cutoff N i M w hh).inv
      (weightedCapMatrixValueEquiv D Sc cutoff N i M _ w z))

/-- The literal weighted cap inverse is the selected OLD inverse. -/
theorem weightedCapPrincipalInverseValue_eq (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0)
    (z : capMatrixTargetSpace D Sc cutoff i RM
      (contentCapCount D cutoff i (w.word : Multiset I)) w) :
    weightedCapPrincipalInverseValue D Sc cutoff N i M w hh z =
    (moduleCapMatrixIso D Sc cutoff RM i w hh).inv z := by
  unfold weightedCapPrincipalInverseValue
  apply (weightedMateSourceLinearEquiv D Sc cutoff N i M w).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (weightedCapInverse_coordinates D Sc cutoff N i M w hh z).symm

/-- The weighted cap principal is the raw negative kernel principal on the
literal upper-Hom coefficient insertion. -/
theorem weightedCapPrincipalInverseValue_tensor (w : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (w.word : Multiset I) ≤ 0)
    (v : OldCategory D Sc cutoff)
    (y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj w) (b : (RM).obj v) :
    weightedCapPrincipalInverseValue D Sc cutoff N i M w hh
      (TensorMatrixCoordinates.negativeKernelCoordinates D Sc cutoff RM i _ w
        (BalancedKernelTensor.tensor _ (RM).toFunctor v (Pi.single none y) b)) =
    IndResKernel.evaluate (append D Sc cutoff i) (RM).toFunctor v w b
      (negativeKernelPrincipalInverse D Sc cutoff i v w hh y) := by
  rw [weightedCapPrincipalInverseValue_eq]
  exact moduleCapMatrixIso_principal_inv_tensor D Sc cutoff RM i w hh v y b

end OddMath.QuiverHecke.ELVOld
