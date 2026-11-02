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

theorem moduleMate_upper_tensor (i j : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    OldInductionRepresentable.equiv D Sc cutoff i
      (⟨v⟩ : OldCategory D Sc cutoff) ((append D Sc cutoff j).obj ⟨t⟩)
      (((moduleMate D Sc cutoff i j).app (D.parity i * D.parity j)
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total ⟨t⟩
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((BalancedInduction.restriction (append D Sc cutoff j)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor ⟨s⟩ g b)) =
      (append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
        (Y := (append D Sc cutoff j).obj ⟨s⟩) b ≫
      crossComponent D Sc cutoff i j ⟨s⟩ ≫
      twist k (D.parity i * D.parity j)
        ((append D Sc cutoff j).map
          (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) (Y := ⟨t⟩) g) := by
  rw [moduleMate_total_tensor]
  exact OldInductionRepresentable.forward_tensor D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) ((append D Sc cutoff j).obj ⟨t⟩)
    ((append D Sc cutoff j).obj ⟨s⟩) _ b

private theorem moduleMate_crossing_word_tensor (i j : I) (v s t : List I)
    (g : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    OldInductionRepresentable.equiv D Sc cutoff i
      (⟨v⟩ : OldCategory D Sc cutoff) ((append D Sc cutoff j).obj ⟨t⟩)
      (((moduleMate D Sc cutoff i j).app (D.parity i * D.parity j)
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total ⟨t⟩
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((BalancedInduction.restriction (append D Sc cutoff j)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor ⟨s⟩ g b)) =
      toCyclotomic D Sc cutoff i j v t
        (moduleSourceParityEquiv D Sc cutoff i j v t
          (BalancedInduction.tensor (append D Sc cutoff i)
            ((BalancedInduction.restriction (append D Sc cutoff j)).obj
              (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor ⟨s⟩ g b)) := by
  rw [moduleMate_upper_tensor, moduleSourceParityEquiv_tensor,
    toCyclotomic_tensor, pairing_eq_append_comp]
  have h := map_twist (R := k) (append D Sc cutoff j) (D.parity i * D.parity j)
    (X := (append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff))
    (Y := (⟨t⟩ : OldCategory D Sc cutoff)) g
  rw [oldCategory_twist] at h
  exact congrArg (fun f :
      (append D Sc cutoff j).obj ((append D Sc cutoff i).obj (⟨s⟩ : OldCategory D Sc cutoff)) ⟶
        (append D Sc cutoff j).obj (⟨t⟩ : OldCategory D Sc cutoff) =>
      (append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
        (Y := (append D Sc cutoff j).obj ⟨s⟩) b ≫ crossComponent D Sc cutoff i j ⟨s⟩ ≫ f) h.symm

/-- The tensor comparison at categorical endpoints avoids rebuilding the
word object inside the balanced induction carrier. -/
theorem moduleMate_crossing_tensor (i j : I) (v : List I)
    (s t : OldCategory D Sc cutoff) (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : ((BalancedInduction.restriction (append D Sc cutoff j)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj s) :
    OldInductionRepresentable.equiv D Sc cutoff i
      (⟨v⟩ : OldCategory D Sc cutoff) ((append D Sc cutoff j).obj t)
      (((moduleMate D Sc cutoff i j).app (D.parity i * D.parity j)
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total t
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((BalancedInduction.restriction (append D Sc cutoff j)).obj
            (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor s g b)) =
      toCyclotomic D Sc cutoff i j v t.word
        (moduleSourceParityEquiv D Sc cutoff i j v t.word
          (BalancedInduction.tensor (append D Sc cutoff i)
            ((BalancedInduction.restriction (append D Sc cutoff j)).obj
              (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor s g b)) := by
  rcases s with ⟨s⟩
  rcases t with ⟨t⟩
  exact moduleMate_crossing_word_tensor D Sc cutoff i j v s t g b

/-- Co-Yoneda evaluation of the literal rectangular mate, with its target
endpoint fixed before comparing source carriers. -/
def evaluatedMate (i j : I) (v t : List I) :
    ModuleSource D Sc cutoff i j v t →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [j]) :=
  (OldInductionRepresentable.equiv D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) ((append D Sc cutoff j).obj ⟨t⟩)).toLinearMap ∘ₗ
    SVec.toLinearMap (((moduleMate D Sc cutoff i j).app (D.parity i * D.parity j)
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).total ⟨t⟩)

private theorem evaluatedMate_tensor (i j : I) (v t : List I)
    (s : OldCategory D Sc cutoff) (g : (append D Sc cutoff i).obj s ⟶ ⟨t⟩)
    (b : ((BalancedInduction.restriction (append D Sc cutoff j)).obj
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).obj s) :
    evaluatedMate D Sc cutoff i j v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff j)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor s g b) =
      toCyclotomic D Sc cutoff i j v t
        (moduleSourceParityEquiv D Sc cutoff i j v t
          (BalancedInduction.tensor (append D Sc cutoff i)
            ((BalancedInduction.restriction (append D Sc cutoff j)).obj
              (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).toFunctor s g b)) := by
  exact moduleMate_crossing_tensor D Sc cutoff i j v s ⟨t⟩ g b

/-- Equality with the prescribed mate on all balanced classes. -/
theorem moduleMate_crossing (i j : I) (v t : List I) :
    evaluatedMate D Sc cutoff i j v t =
      toCyclotomic D Sc cutoff i j v t ∘ₗ (moduleSourceParityEquiv D Sc cutoff i j v t).toLinearMap := by
  apply BalancedInduction.hom_ext
  intro s g b
  exact evaluatedMate_tensor D Sc cutoff i j v t s g b

/-- The explicit mixed PBW inverse attached to the prescribed categorical mate
on old representables. -/
def moduleMateEquiv (i j : I) (hij : i ≠ j) (v t : List I) :
    ModuleSource D Sc cutoff i j v t ≃ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [j]) :=
  (moduleSourceParityEquiv D Sc cutoff i j v t).trans (cyclotomicEquiv D Sc cutoff i j hij v t)

/-- The constructed equivalence is the evaluated literal cup-crossing-cap. -/
theorem moduleMateEquiv_apply (i j : I) (hij : i ≠ j) (v t : List I)
    (z : ModuleSource D Sc cutoff i j v t) :
    moduleMateEquiv D Sc cutoff i j hij v t z = evaluatedMate D Sc cutoff i j v t z :=
  (LinearMap.congr_fun (moduleMate_crossing D Sc cutoff i j v t) z).symm

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
