/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldModuleAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionMixedMateTensor
import OddMath.SKM.RouquierMixedMate
import StringDiagrams.Super.SCat

/-! # The old two-colour crossing and its prescribed mate

The positive distinct-colour crossing and the even balanced-induction
adjunction give the literal cup-crossing-cap of Brundan–Ellis (1.12).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def crossComponent (i j : I) (s : OldCategory D Sc cutoff) :
    ((append D Sc cutoff j) ⋙ (append D Sc cutoff i)).obj s ⟶
      ((append D Sc cutoff i) ⋙ (append D Sc cutoff j)).obj s :=
  (ideal D Sc cutoff _ _).mkQ
    (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word j i))

theorem cross_supernatural (i j : I) :
    IsSupernatural k (D.parity i * D.parity j)
      (F := (append D Sc cutoff j) ⋙ (append D Sc cutoff i))
      (G := (append D Sc cutoff i) ⋙ (append D Sc cutoff j))
      (crossComponent D Sc cutoff i j) := by
  apply IsSupernatural.of_twist
  · intro s
    have hc := ELVPScalar.affineUnit_mem D Sc cutoff (crossLast_mem D Sc s.word j i)
    rw [mul_comm (D.parity j) (D.parity i)] at hc
    exact Submodule.mem_map_of_mem hc
  · intro s t f

    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s.word t.word).mkQ_surjective f
    have htw : twist k (D.parity i * D.parity j) (X := s) (Y := t)
        (((ideal D Sc cutoff s.word t.word).mkQ r) : s ⟶ t) =
        ((ideal D Sc cutoff s.word t.word).mkQ (twist k (D.parity i * D.parity j) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r) : s ⟶ t) := by
      rw [twist_apply, oldCategory_proj, oldCategory_proj]
      change (ideal D Sc cutoff s.word t.word).mkQ (proj k 0 r) +
        sign k (D.parity i * D.parity j) • (ideal D Sc cutoff s.word t.word).mkQ (proj k 1 r) =
        (ideal D Sc cutoff s.word t.word).mkQ (twist k (D.parity i * D.parity j) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r)
      rw [twist_apply, map_add, map_smul]
    rw [htw]
    change (ideal D Sc cutoff (s.word ++ [j] ++ [i]) (t.word ++ [i] ++ [j])).mkQ
      (rightContext D Sc cutoff [i] _ _ (rightContext D Sc cutoff [j] _ _ r) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc t.word j i)) =
      (ideal D Sc cutoff (s.word ++ [j] ++ [i]) (t.word ++ [i] ++ [j])).mkQ
        (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word j i) ≫
          rightContext D Sc cutoff [j] _ _
            (rightContext D Sc cutoff [i] _ _ (twist k (D.parity i * D.parity j) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r)))
    have h := crossLast_comp_rightContext D Sc cutoff j i
      (twist k (D.parity i * D.parity j) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r)
    rw [mul_comm (D.parity j) (D.parity i), twist_twist] at h
    exact congrArg
      (ideal D Sc cutoff (s.word ++ [j] ++ [i]) (t.word ++ [i] ++ [j])).mkQ h.symm

/-- Positive two-colour crossing under the canonical induction comparisons. -/
def moduleCross (i j : I) :
    oldInduction D Sc cutoff i ≫ oldInduction D Sc cutoff j ⟶
      oldInduction D Sc cutoff j ≫ oldInduction D Sc cutoff i :=
  Superfunctor.homMk (BalancedInduction.mixedCrossComponent_supernatural
    (append D Sc cutoff i) (append D Sc cutoff j) (cross_supernatural D Sc cutoff i j)).toSuperNatTrans

@[simp] theorem moduleCross_app (i j : I) (r : ZMod 2)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (moduleCross D Sc cutoff i j).app r N =
      if r = D.parity i * D.parity j then
        BalancedInduction.mixedCrossComponent (append D Sc cutoff i) (append D Sc cutoff j)
          (cross_supernatural D Sc cutoff i j) N else 0 := rfl

/-- The prescribed rectangular cup-crossing-cap, using the fixed even adjunction. -/
def moduleMate (i j : I) :
    oldRestriction D Sc cutoff j ≫ oldInduction D Sc cutoff i ⟶
      oldInduction D Sc cutoff i ≫ oldRestriction D Sc cutoff j :=
  SKM.rectangularMate (k := k) (B := SCat.{u,u,u + 1} k)
    (oldAppendAdjunction D Sc cutoff j) (oldAppendAdjunction D Sc cutoff j)
    (oldInduction D Sc cutoff i) (oldInduction D Sc cutoff i) (moduleCross D Sc cutoff i j)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
