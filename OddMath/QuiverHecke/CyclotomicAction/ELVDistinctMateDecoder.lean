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
