import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCoefficientModule
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedAppendTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVPCentral

/-! # The actual odd dot on the old append superfunctor
The same full-coefficient appended component used by the truncated action
descends to the existing old quotient and is supernatural there.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def oldAppendDotComponent (i : I) (s : OldCategory D Sc cutoff) :
    (append D Sc cutoff i).obj s ⟶ (append D Sc cutoff i).obj s :=
  (ideal D Sc cutoff _ _).mkQ
    (appendComponent D Sc cutoff (dotE D Sc [i] 0) s.word)

theorem oldAppendDotComponent_eq (i : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i s =
      (ideal D Sc cutoff _ _).mkQ (appendMovingPower D Sc cutoff i s.word 1) := by
  simp only [oldAppendDotComponent, appendMovingPower_whisker, pow_one,
    appendComponent]
  rfl

theorem oldAppendDot_supernatural (i : I) :
    IsSupernatural k (D.parity i) (oldAppendDotComponent D Sc cutoff i) where
  mem s := Submodule.mem_map_of_mem (appendComponent_mem D Sc cutoff
    (by simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1) s.word)
  naturality := by
    rintro s t q f ⟨a, ha, rfl⟩
    have h := congrArg (ideal D Sc cutoff (s.word ++ [i]) (t.word ++ [i])).mkQ
      (appendComponent_naturality D Sc cutoff
        (by simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1) ha)
    rw [map_zsmul, koszulSign_smul (R := k)] at h
    exact h

def inductionDot (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (append D Sc cutoff i) M.toFunctor t →ₗ[k]
      BalancedInduction.Obj (append D Sc cutoff i) M.toFunctor t :=
  BalancedInduction.transformLinear (oldAppendDot_supernatural D Sc cutoff i) M t

@[simp] theorem inductionDot_tensor (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : M.obj s) :
    inductionDot D Sc cutoff i M t
      (BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor s g b) =
      BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor s
        (oldAppendDotComponent D Sc cutoff i s ≫ twist k (D.parity i) g) b :=
  BalancedInduction.transformLinear_tensor _ _ _ _ _ _

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
