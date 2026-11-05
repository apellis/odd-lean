import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform
import Mathlib.CategoryTheory.EqToHom
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionComp
import OddMath.QuiverHecke.CyclotomicAction.ELVContentCompositeComparison

/-! # The equal-colour crossing through the weighted quotient

DeformedActionAssembly §5 and DeformedMatrixComparison (2), (4) require the
last-strand crossing, with the prescribed sign, on the chosen two-induction
comparison. The literal quotient of `crossLast` is identified with the
existing `crossTwo` append component under word associativity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem mapFamily_heq {ι : Type*} {A B : ι → Type*}
    (F : ∀ i, A i → B i) {i j : ι} (h : i = j)
    {a : A i} {b : A j} (hab : HEq a b) : HEq (F i a) (F j b) := by
  cases h
  cases hab
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I)
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "T" => truncatedAppend D Sc cutoff N [i]

/-- The crossing at the last two positions on successive singleton appends. -/
def truncatedEqualCrossComponent (s : TruncatedCategory D Sc cutoff N) :
    (T ⋙ T).obj s ⟶ (T ⋙ T).obj s :=
  (truncatedIdeal D Sc cutoff N _ _).mkQ
    (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i))

/-- Quotienting retains the literal affine crossing. -/
theorem oldTruncateFunctor_map_equalCross (s : OldCategory D Sc cutoff) :
    (Q).map (CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s) =
      truncatedEqualCrossComponent D Sc cutoff N i ((Q).obj s) := rfl

/-- This is the existing appended `crossTwo`, with only word associativity
changing its endpoints. In particular no alternate crossing is selected. -/
theorem truncatedEqualCrossComponent_heq (s : TruncatedCategory D Sc cutoff N) :
    HEq (truncatedEqualCrossComponent D Sc cutoff N i s)
      (truncatedAppendComponent D Sc cutoff N (crossTwo D Sc i i) s) := by
  have hw : (s.word ++ [i] ++ [i], s.word ++ [i] ++ [i]) =
      (s.word ++ [i, i], s.word ++ [i, i]) := by simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hc := (conj_eqToHom_iff_heq _ _
    (congrArg (fun w => (pres D Sc).obj (ob D w)) (List.append_assoc s.word [i] [i]))
    (congrArg (fun w => (pres D Sc).obj (ob D w)) (List.append_assoc s.word [i] [i]))).mp
      (crossLast_eq D Sc s.word i i)
  have ha := mapFamily_heq
    (A := fun z : List I × List I =>
      (pres D Sc).obj (ob D z.1) ⟶ (pres D Sc).obj (ob D z.2))
    (B := fun z : List I × List I => hom D Sc cutoff z.1 z.2)
    (fun z f => affineUnit D Sc cutoff z.1 z.2 f) hw hc
  exact mapFamily_heq
    (A := fun z : List I × List I => hom D Sc cutoff z.1 z.2)
    (B := fun z : List I × List I => TruncatedOld D Sc cutoff N z.1 z.2)
    (fun z f => (truncatedIdeal D Sc cutoff N z.1 z.2).mkQ f) hw ha

/-- Full coefficient supernaturality descends from the old crossing. -/
theorem truncatedEqualCross_supernatural :
    IsSupernatural k (D.parity i * D.parity i)
      (truncatedEqualCrossComponent D Sc cutoff N i) := by
  apply IsSupernatural.of_twist
  · intro s
    exact Submodule.mem_map_of_mem
      (ELVPScalar.affineUnit_mem D Sc cutoff (crossLast_mem D Sc s.word i i))
  · intro s t f
    obtain ⟨a, rfl⟩ := (truncatedIdeal D Sc cutoff N s.word t.word).mkQ_surjective f
    let f' : (⟨s.word⟩ : OldCategory D Sc cutoff) ⟶ ⟨t.word⟩ :=
      (ideal D Sc cutoff s.word t.word).mkQ a
    have h := congrArg (fun g => (Q).map g)
      ((CyclotomicCrossingTensor.equalCross_supernatural D Sc cutoff i).naturality_twist f')
    simp only [Functor.map_comp, map_twist] at h
    rw [map_twist]
    exact h

variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

/-- The selected pair comparison intertwines the prescribed crossing on
composed induction, retaining the twist on arbitrary coefficient arrows. -/
theorem pairWeightedModuleIso_hom_crossing (w : OldCategory D Sc cutoff) :
    pairAppendComparisonLinear D Sc cutoff N i i M w ∘ₗ
        BalancedInduction.transformLinear
          (CyclotomicCrossingTensor.equalCross_supernatural D Sc cutoff i) RM w =
      BalancedInduction.transformLinear (truncatedEqualCross_supernatural D Sc cutoff N i)
        M ((Q).obj w) ∘ₗ pairAppendComparisonLinear D Sc cutoff N i i M w := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, BalancedInduction.transformLinear_tensor,
    pairWeightedModuleIso_hom_tensor]
  rw [(Q).map_comp, map_twist, oldTruncateFunctor_map_equalCross]
  rfl

/-- The prescribed extra minus in the action crossing is preserved. -/
theorem pairWeightedModuleIso_hom_signedCrossing (w : OldCategory D Sc cutoff) :
    pairAppendComparisonLinear D Sc cutoff N i i M w ∘ₗ
        (-BalancedInduction.transformLinear
          (CyclotomicCrossingTensor.equalCross_supernatural D Sc cutoff i) RM w) =
      (-BalancedInduction.transformLinear (truncatedEqualCross_supernatural D Sc cutoff N i)
        M ((Q).obj w)) ∘ₗ pairAppendComparisonLinear D Sc cutoff N i i M w := by
  rw [LinearMap.comp_neg, LinearMap.neg_comp,
    pairWeightedModuleIso_hom_crossing D Sc cutoff N i M w]

end OddMath.QuiverHecke.ELVOld
