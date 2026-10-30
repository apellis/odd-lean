/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerMeet
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerNaturality

/-!
# Crossing naturality of reverse moving chains

The reverse-direction old-crossing identity associated to Kang–Kashiwara–Oh
Lemma 8.3 and (8.13), for arbitrary surrounding words and all colour coincidences.
The factors are `reverseMoveHom`; no inverse or assumed transport is used.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open SKM (zsign)
variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- A crossing in the fixed prefix supercommutes with a reverse moving chain. -/
theorem cross_left_comp_reverseMoveHom (i x y : I) (l₁ ν : List I) :
    ∀ (L L' l₂ : List I) (hL : L = l₁ ++ [x, y] ++ l₂) (hL' : L' = l₁ ++ [y, x] ++ l₂),
      cl D Sc (L ++ ν ++ [i]) (L' ++ ν ++ [i]) [.cross l₁.length]
          (by simpa only [List.append_assoc] using
            sChain_cross_split (s := ν ++ [i]) hL hL') ≫ reverseMoveHom D Sc i L' ν =
        zsign k (D.parity x * D.parity y * (D.parity i * wordSumParity D ν)) •
          (reverseMoveHom D Sc i L ν ≫
            cl D Sc (L ++ i :: ν) (L' ++ i :: ν) [.cross l₁.length]
              (sChain_cross_split hL hL')) := by
  induction ν with
  | nil =>
    intro L L' l₂ hL hL'
    simp only [reverseMoveHom, wordSumParity, List.map_nil, List.sum_nil, mul_zero]
    rw [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul,
      cl_comp_eqToHom, eqToHom_comp_cl]
    all_goals simp
  | cons j ν ih =>
    intro L L' l₂ hL hL'
    subst hL hL'
    simp only [reverseMoveHom]
    rw [← Category.assoc, cl_comp_eqToHom D Sc _
        (show (l₁ ++ [y, x] ++ l₂) ++ (j :: ν) ++ [i] =
          (l₁ ++ [y, x] ++ l₂ ++ [j]) ++ ν ++ [i] by simp),
      cl_eq_eqToHom_comp D Sc
        (show (l₁ ++ [x, y] ++ l₂) ++ (j :: ν) ++ [i] =
          (l₁ ++ [x, y] ++ l₂ ++ [j]) ++ ν ++ [i] by simp),
      Category.assoc, ← Category.assoc (cl D Sc _ _ _ _),
      ih (l₁ ++ [x, y] ++ l₂ ++ [j]) (l₁ ++ [y, x] ++ l₂ ++ [j]) (l₂ ++ [j])
        (by simp) (by simp),
      Linear.smul_comp, Linear.comp_smul, Category.assoc,
      ← Category.assoc (cl D Sc _ _ _ _), cl_comp_eqToHom D Sc _
        (show (l₁ ++ [y, x] ++ l₂ ++ [j]) ++ i :: ν =
          (l₁ ++ [y, x] ++ l₂) ++ [j, i] ++ ν by simp),
      cl_eq_eqToHom_comp D Sc
        (show (l₁ ++ [x, y] ++ l₂ ++ [j]) ++ i :: ν =
          (l₁ ++ [x, y] ++ l₂) ++ [j, i] ++ ν by simp),
      Category.assoc, ← Category.assoc (cl D Sc _ _ _ _),
      cross_left_comp_intertwinerHom, Linear.smul_comp, Linear.comp_smul,
      Category.assoc, cl_comp_eqToHom]
    simp only [Category.assoc]
    rw [eqToHom_comp_cl]
    · simp only [Linear.comp_smul, smul_smul, ← zsign_add_eq, wordSumParity,
        List.map_cons, List.sum_cons]
      exact congrArg (fun z => zsign k z • _) (by ring)
    all_goals simp

/-- The crossing adjacent to the old-word boundary passes through the reverse chain. -/
theorem cross_comp_reverseMoveHom_base (l v : List I) (i j c : I)
    (h₁ : SChain (l ++ (j :: c :: v) ++ [i])
      (pl (l ++ (j :: c :: v) ++ [i]) [.cross l.length]) (l ++ (c :: j :: v) ++ [i]))
    (h₂ : SChain (l ++ i :: j :: c :: v)
      (pl (l ++ i :: j :: c :: v) [.cross (l.length + 1)]) (l ++ i :: c :: j :: v)) :
    cl D Sc _ _ [.cross l.length] h₁ ≫ reverseMoveHom D Sc i l (c :: j :: v) =
      zsign k (D.parity j * D.parity c * (D.parity i * wordSumParity D v)) •
        (reverseMoveHom D Sc i l (j :: c :: v) ≫
          cl D Sc _ _ [.cross (l.length + 1)] h₂) := by
  have hc := cross_left_comp_reverseMoveHom D Sc i j c l v (l ++ [j] ++ [c])
    (l ++ [c] ++ [j]) [] (by simp) (by simp)
  have hm := reverseMeetLeft_eq_all D Sc l v i j c
  unfold reverseMeetLeft reverseMeetRight ReverseIntertwinerMeet.g0
    ReverseIntertwinerMeet.g1 ReverseIntertwinerMeet.p0 ReverseIntertwinerMeet.p1 at hm
  simp only [Category.assoc, eqToHom_trans_assoc] at hm
  simp only [reverseMoveHom, Category.assoc, eqToHom_trans_assoc]
  rw [cl_comp_eqToHom_assoc, cl_eq_eqToHom_comp D Sc
    (show l ++ (j :: c :: v) ++ [i] = (l ++ [j] ++ [c]) ++ v ++ [i] by simp),
    Category.assoc, reassoc_of% hc]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc]
  congr 1
  have hm' := congrArg (fun f =>
    eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s))
      (show (l ++ [j] ++ [c]) ++ i :: v = l ++ j :: c :: i :: v by simp)) ≫ f) hm
  simp only [eqToHom_trans_assoc] at hm'
  rw [eqToHom_comp_cl_assoc, cl_comp_eqToHom_assoc] at hm'
  · rw [cl_comp_eqToHom_assoc]
    · exact congrArg (fun f => eqToHom _ ≫ reverseMoveHom D Sc i (l ++ [j] ++ [c]) v ≫ f) hm'
    · simp
  all_goals simp

/-- Every old crossing passes through the reverse moving chain, including all colour
coincidences, with the parity of the old strands outside the crossing. -/
theorem cross_comp_reverseMoveHom_all (v : List I) (i j c : I) (m : List I) :
    ∀ l : List I,
      cl D Sc _ _ [.cross (l.length + m.length)] (sChain_mid₂ l m v i j c) ≫
          reverseMoveHom D Sc i l (m ++ c :: j :: v) =
        zsign k (D.parity j * D.parity c * (D.parity i * (wordSumParity D m + wordSumParity D v))) •
          (reverseMoveHom D Sc i l (m ++ j :: c :: v) ≫
            cl D Sc _ _ [.cross (l.length + 1 + m.length)] (sChain_mid₁ l m v i j c)) := by
  induction m with
  | nil =>
    intro l
    have hw : wordSumParity D ([] : List I) = 0 := by simp [wordSumParity]
    rw [hw, zero_add]
    exact cross_comp_reverseMoveHom_base D Sc l v i j c _ _
  | cons x m ih =>
    intro l
    simp only [List.cons_append, reverseMoveHom]
    rw [← Category.assoc, cl_comp_eqToHom D Sc _
        (show l ++ (x :: (m ++ c :: j :: v)) ++ [i] =
          (l ++ [x]) ++ (m ++ c :: j :: v) ++ [i] by simp),
      cl_eq_eqToHom_comp D Sc
        (show l ++ (x :: (m ++ j :: c :: v)) ++ [i] =
          (l ++ [x]) ++ (m ++ j :: c :: v) ++ [i] by simp),
      cl_cross_pos D Sc (p' := (l ++ [x]).length + m.length) (by simp; omega),
      Category.assoc, ← Category.assoc (cl D Sc _ _ _ _), ih (l ++ [x]),
      Linear.smul_comp, Linear.comp_smul, Category.assoc,
      ← Category.assoc (cl D Sc _ _ _ _), cl_comp_eqToHom D Sc _
        (show (l ++ [x]) ++ i :: (m ++ c :: j :: v) = l ++ [x, i] ++ (m ++ c :: j :: v) by simp),
      cl_eq_eqToHom_comp D Sc
        (show (l ++ [x]) ++ i :: (m ++ j :: c :: v) = l ++ [x, i] ++ (m ++ j :: c :: v) by simp),
      cl_cross_pos D Sc (p' := (l ++ [x, i] ++ m).length) (by simp; omega),
      Category.assoc, ← Category.assoc (cl D Sc _ _ _ _), cross_right_comp_intertwinerHom,
      Linear.smul_comp, Linear.comp_smul, Category.assoc, cl_comp_eqToHom]
    simp only [Category.assoc]
    rw [eqToHom_comp_cl, cl_cross_pos D Sc (p := l.length + 1 + (x :: m).length)
      (p' := (l ++ [i, x] ++ m).length) (by simp; omega)]
    · simp only [Linear.comp_smul, smul_smul, ← zsign_add_eq, wordSumParity,
        List.map_cons, List.sum_cons]
      exact congrArg (fun z => zsign k z • _) (by ring)
    all_goals simp

end OddMath.QuiverHecke
