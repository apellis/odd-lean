/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleMate
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctSourceParity
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctCrossingQuotient
import OddMath.QuiverHecke.CyclotomicAction.ELVOldInductionRepresentable
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations

/-! # The prescribed distinct mate and the cyclotomic crossing decoder

Brundan–Ellis (1.12), via `DeformedActionAssembly.md` §4: the literal positive
cup-crossing-cap equals the checked crossing isomorphism after canonical J.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

abbrev ModuleSource (i j : I) (v t : List I) :=
  ((BalancedInduction.induction (append D Sc cutoff i)).obj
    ((BalancedInduction.restriction (append D Sc cutoff j)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
        (⟨t⟩ : OldCategory D Sc cutoff)

/-- The canonical coefficient-zero identification, induced from the fixed module iso. -/
def moduleSourceZeroEquiv (i j : I) (v t : List I) :
    ModuleSource D Sc cutoff i j v t ≃ₗ[k] SourceWithParity D Sc cutoff 0 i j v t :=
  moduleIsoLinearEquiv
    (((BalancedInduction.induction (append D Sc cutoff i)).mapIso
      (coefficientRestrictionModuleIso D Sc cutoff j v)).symm)
    (⟨t⟩ : OldCategory D Sc cutoff)

private theorem coefficientRestriction_inv_app (j : I) (v : List I) (q : ZMod 2)
    (s : OldCategory D Sc cutoff) :
    (coefficientRestrictionModuleIso D Sc cutoff j v).inv.app q s =
      if q = 0 then LinearMap.id else 0 := rfl

@[simp] theorem moduleSourceZeroEquiv_tensor (i j : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    moduleSourceZeroEquiv D Sc cutoff i j v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff j)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor ⟨s⟩ g b) =
      parityTensor D Sc cutoff 0 i j v s t g b := by
  have h := BalancedInduction.moduleMap_total_tensor (append D Sc cutoff i)
    (coefficientRestrictionModuleIso D Sc cutoff j v).inv
    (⟨t⟩ : OldCategory D Sc cutoff) (⟨s⟩ : OldCategory D Sc cutoff) g b
  rw [coefficientRestriction_inv_app, coefficientRestriction_inv_app] at h
  simp only [↓reduceIte, one_ne_zero] at h
  change _ = BalancedInduction.tensor (append D Sc cutoff i)
      (coefficientZeroModule D Sc cutoff j v).toFunctor (⟨s⟩ : OldCategory D Sc cutoff) g b +
    BalancedInduction.tensor (append D Sc cutoff i) (coefficientZeroModule D Sc cutoff j v).toFunctor
      (⟨s⟩ : OldCategory D Sc cutoff) (twist k 1 g) (0 : Old D Sc cutoff v (s ++ [j])) at h
  rw [BalancedInduction.tensor_zero_right, add_zero] at h
  exact h

/-- The prescribed J twists the whole first factor, including exterior coefficients. -/
def moduleSourceParityEquiv (i j : I) (v t : List I) :
    ModuleSource D Sc cutoff i j v t ≃ₗ[k] Source D Sc cutoff i j v t :=
  (moduleSourceZeroEquiv D Sc cutoff i j v t).trans (sourceParityEquiv D Sc cutoff i j v t)

@[simp] theorem moduleSourceParityEquiv_tensor (i j : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    moduleSourceParityEquiv D Sc cutoff i j v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff j)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor ⟨s⟩ g b) =
      tensor D Sc cutoff i j v s t
        (oldTwist D Sc cutoff (D.parity i * D.parity j) (s ++ [i]) t g) b := by
  rw [moduleSourceParityEquiv, LinearEquiv.trans_apply, moduleSourceZeroEquiv_tensor]
  change parityTransport D Sc cutoff 0 _ i j v t (parityTensor D Sc cutoff 0 i j v s t g b) = _
  rw [parityTransport_tensor, zero_add]
  rfl

theorem pairing_eq_append_comp (i j : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    pairing D Sc cutoff i j v s t g b =
      (append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
        (Y := (append D Sc cutoff j).obj ⟨s⟩) b ≫
        crossComponent D Sc cutoff i j ⟨s⟩ ≫
        (append D Sc cutoff j).map
          (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) (Y := ⟨t⟩) g := by
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff (s ++ [i]) t).mkQ_surjective g
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [j])).mkQ_surjective b
  rfl

/-- Co-Yoneda evaluation of the literal rectangular mate, with its target
endpoint fixed before comparing source carriers. -/
def evaluatedMate (i j : I) (v t : List I) :
    ModuleSource D Sc cutoff i j v t →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [j]) :=
  (OldInductionRepresentable.equiv D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) ((append D Sc cutoff j).obj ⟨t⟩)).toLinearMap ∘ₗ
    SVec.toLinearMap (((moduleMate D Sc cutoff i j).app (D.parity i * D.parity j)
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total ⟨t⟩)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
