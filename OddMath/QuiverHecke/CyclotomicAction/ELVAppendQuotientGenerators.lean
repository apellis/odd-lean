import OddMath.QuiverHecke.CyclotomicAction.ELVAppendQuotientTensors

/-! # Generators of the weighted append comparison
The canonical comparison of SwappedVacuumCoordinates §6 is evaluated on
the literal old balanced tensors before transporting the action generators.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {k : Type u} [CommRing k]
  {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

private theorem iso_chain_total
    {F₀ F₁ F₂ F₃ F₄ F₅ : Superfunctor k C (SVec k)}
    (e₁ : F₀ ≅ F₁) (e₂ : F₁ ≅ F₂) (e₃ : F₂ ≅ F₃)
    (e₄ : F₃ ≅ F₄) (e₅ : F₄ ≅ F₅) (w : C) (x : F₀.obj w) :
    (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅).hom.total w x =
      e₅.hom.total w (e₄.hom.total w (e₃.hom.total w
        (e₂.hom.total w (e₁.hom.total w x)))) := by
  simp only [Iso.trans_hom, Superfunctor.comp_total, LinearMap.comp_apply]

end OddMath.QuiverHecke.ELVOld

namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]

theorem moduleMap_total_tensor_even
    {M L : Superfunctor k C (SVec k)} (f : M ⟶ L)
    (hf : f ∈ parity (R := k) _ _ 0) (w : D) (v : C)
    (g : J.obj v ⟶ w) (b : M.obj v) :
    (moduleMap J f).total w (tensor J M.toFunctor v g b) =
      tensor J L.toFunctor v g (f.app 0 v b) := by
  rw [moduleMap_total_tensor, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide),
    LinearMap.zero_apply, tensor_zero_right, add_zero]

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
local notation "Q" => oldTruncateFunctor D Sc cutoff N

/-- The original old tensor, with its target descended on unchanged vectors. -/
def weightedAppendTensor (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (s : OldCategory D Sc cutoff) (w : TruncatedCategory D Sc cutoff N)
    (g : (CyclotomicCrossingTensor.append D Sc cutoff i).obj s ⟶
      (⟨w.word⟩ : OldCategory D Sc cutoff)) (b : M.obj (Q.obj s)) :
    ((weightedAppendFunctor D Sc cutoff N i).obj M).obj w :=
  BalancedInduction.tensor (CyclotomicCrossingTensor.append D Sc cutoff i)
    (weightedRestriction D Sc cutoff N M).toFunctor s g b

theorem quotientCounit_moduleMap_unit_tensor (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (s : OldCategory D Sc cutoff) (w : TruncatedCategory D Sc cutoff N)
    (g : (truncatedAppend D Sc cutoff N [i]).obj (Q.obj s) ⟶ w)
    (b : M.obj (Q.obj s)) :
    ((BalancedInduction.induction (truncatedAppend D Sc cutoff N [i])).map
      (quotientInductionCounitIso D Sc cutoff N M).hom).total w
        (BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i])
          (BalancedInduction.induced Q (weightedRestriction D Sc cutoff N M)).toFunctor
          (Q.obj s) g
          (BalancedInduction.unit Q (weightedRestriction D Sc cutoff N M).toFunctor s b)) =
      BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i]) M.toFunctor (Q.obj s) g b := by
  have hf : (quotientInductionCounitIso D Sc cutoff N M).hom ∈ parity (R := k) _ _ 0 := by
    rw [quotientInductionCounitIso_hom]
    exact BalancedInduction.adjunctionCounit_mem Q M
  change (BalancedInduction.moduleMap (truncatedAppend D Sc cutoff N [i])
    (quotientInductionCounitIso D Sc cutoff N M).hom).total w _ = _
  rw [BalancedInduction.moduleMap_total_tensor_even _ _ hf]
  have hb : (quotientInductionCounitIso D Sc cutoff N M).hom.app 0 (Q.obj s)
      (BalancedInduction.unit Q (weightedRestriction D Sc cutoff N M).toFunctor s b) = b := by
    change BalancedInduction.counit Q M.toFunctor (Q.obj s)
      (BalancedInduction.unit Q (Q ⋙ M.toFunctor) s b) = b
    exact LinearMap.congr_fun (BalancedInduction.counit_unit Q M.toFunctor s) b
  exact congrArg (BalancedInduction.tensor (truncatedAppend D Sc cutoff N [i]) M.toFunctor
    (Q.obj s) g) hb

end OddMath.QuiverHecke.ELVOld
