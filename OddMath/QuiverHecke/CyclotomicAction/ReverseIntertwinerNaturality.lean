/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerChain

/-!
# Dot naturality of reverse moving chains

Reverse-direction dot transport for the moving chains of Kang–Kashiwara–Oh.
`dot_mem_comp_reverseMoveHom` supplies the old-dot case required for reverse
old-ideal descent. The crossing theorem below covers only two old strands
which both differ from the moving colour; unrestricted descent is not asserted.
No inverse to an intertwiner is used.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open SKM (zsign)
variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- The moving dot passes from the append endpoint back to the prepend endpoint. -/
theorem dot_comp_reverseMoveHom (i : I) (l ν : List I) :
    dotE D Sc (l ++ ν ++ [i]) (l.length + ν.length) ≫ reverseMoveHom D Sc i l ν =
      zsign k (D.parity i * wordSumParity D ν) •
        (reverseMoveHom D Sc i l ν ≫ dotE D Sc (l ++ i :: ν) l.length) := by
  induction ν generalizing l with
  | nil =>
    simp only [reverseMoveHom, wordSumParity, List.map_nil, List.sum_nil, mul_zero,
      List.length_nil, add_zero]
    rw [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul]
    exact dotE_comp_eqToHom D Sc (by simp) _
  | cons j ν ih =>
    simp only [reverseMoveHom]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc
        (show l ++ (j :: ν) ++ [i] = (l ++ [j]) ++ ν ++ [i] by simp),
      Category.assoc, show l.length + (j :: ν).length = (l ++ [j]).length + ν.length by simp; omega,
      ← Category.assoc (dotE D Sc _ _), ih, Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc
        (show (l ++ [j]) ++ i :: ν = l ++ [j, i] ++ ν by simp),
      show (l ++ [j]).length = l.length + 1 by simp,
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_succ_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc,
      dotE_comp_eqToHom D Sc (show l ++ [i, j] ++ ν = l ++ i :: j :: ν by simp)]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, wordSumParity, List.map_cons,
      List.sum_cons, mul_add, zsign_add_eq, mul_comm]

/-- A fixed dot strictly to the left of the chain supercommutes with the reverse chain. -/
theorem dot_left_comp_reverseMoveHom (i x : I) (l₁ : List I) (ν : List I) :
    ∀ (l l₂ : List I), l = l₁ ++ [x] ++ l₂ →
      dotE D Sc (l ++ ν ++ [i]) l₁.length ≫ reverseMoveHom D Sc i l ν =
        zsign k (D.parity x * (D.parity i * wordSumParity D ν)) •
          (reverseMoveHom D Sc i l ν ≫ dotE D Sc (l ++ i :: ν) l₁.length) := by
  induction ν with
  | nil =>
    intro l l₂ _
    simp only [reverseMoveHom, wordSumParity, List.map_nil, List.sum_nil, mul_zero]
    rw [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul]
    exact dotE_comp_eqToHom D Sc (by simp) _
  | cons j ν ih =>
    intro l l₂ hl
    subst hl
    simp only [reverseMoveHom]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc
        (show (l₁ ++ [x] ++ l₂) ++ (j :: ν) ++ [i] =
          (l₁ ++ [x] ++ l₂ ++ [j]) ++ ν ++ [i] by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _),
      ih (l₁ ++ [x] ++ l₂ ++ [j]) (l₂ ++ [j]) (by simp),
      Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc
        (show (l₁ ++ [x] ++ l₂ ++ [j]) ++ i :: ν =
          (l₁ ++ [x] ++ l₂) ++ [j, i] ++ ν by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_left_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc,
      dotE_comp_eqToHom D Sc
        (show (l₁ ++ [x] ++ l₂) ++ [i, j] ++ ν =
          (l₁ ++ [x] ++ l₂) ++ i :: j :: ν by simp)]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, wordSumParity, List.map_cons,
      List.sum_cons, mul_add, zsign_add_eq, mul_comm, mul_left_comm]

/-- Every old-strand dot passes through the reverse chain with its full word-parity sign. -/
theorem dot_mem_comp_reverseMoveHom (i x : I) (v : List I) (m : List I) :
    ∀ (l ν : List I), ν = m ++ [x] ++ v →
      dotE D Sc (l ++ ν ++ [i]) (l.length + m.length) ≫ reverseMoveHom D Sc i l ν =
        zsign k (D.parity x * (D.parity i * wordSumParity D ν)) •
          (reverseMoveHom D Sc i l ν ≫ dotE D Sc (l ++ i :: ν) (l.length + 1 + m.length)) := by
  induction m with
  | nil =>
    intro l ν hν
    obtain rfl : ν = x :: v := by simp [hν]
    simp only [reverseMoveHom, List.length_nil, add_zero]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc
        (show l ++ (x :: v) ++ [i] = (l ++ [x]) ++ v ++ [i] by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dot_left_comp_reverseMoveHom D Sc i x l v (l ++ [x]) [] (by simp),
      Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc (show (l ++ [x]) ++ i :: v = l ++ [x, i] ++ v by simp),
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc,
      dotE_comp_eqToHom D Sc (show l ++ [i, x] ++ v = l ++ i :: x :: v by simp)]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, ← zsign_add_eq]
    congr 2
    simp only [wordSumParity, List.map_cons, List.sum_cons]
    linear_combination (-D.parity i) * parity_sq (D.parity x)
  | cons j m ih =>
    intro l ν hν
    obtain rfl : ν = j :: (m ++ [x] ++ v) := by simp [hν]
    simp only [reverseMoveHom]
    rw [← Category.assoc, dotE_comp_eqToHom D Sc
        (show l ++ (j :: (m ++ [x] ++ v)) ++ [i] =
          (l ++ [j]) ++ (m ++ [x] ++ v) ++ [i] by simp),
      Category.assoc,
      show l.length + (j :: m).length = (l ++ [j]).length + m.length by simp; omega,
      ← Category.assoc (dotE D Sc _ _), ih (l ++ [j]) _ rfl,
      Linear.smul_comp, Category.assoc, ← Category.assoc (dotE D Sc _ _),
      dotE_comp_eqToHom D Sc
        (show (l ++ [j]) ++ i :: (m ++ [x] ++ v) = l ++ [j, i] ++ (m ++ [x] ++ v) by simp),
      show (l ++ [j]).length + 1 + m.length = (l ++ [j, i] ++ m).length by simp; omega,
      Category.assoc, ← Category.assoc (dotE D Sc _ _), dot_right_comp_intertwinerHom,
      Linear.smul_comp, Category.assoc,
      dotE_comp_eqToHom D Sc
        (show l ++ [i, j] ++ (m ++ [x] ++ v) = l ++ i :: j :: (m ++ [x] ++ v) by simp),
      show (l ++ [j, i] ++ m).length = l.length + 1 + (j :: m).length by simp; omega]
    simp only [Linear.comp_smul, smul_smul, Category.assoc, wordSumParity, List.map_cons,
      List.sum_cons, mul_add, zsign_add_eq, mul_comm, mul_left_comm]

/-- Reverse crossing naturality on two old strands when both differ from the moving colour.
The repeated-old-colour case is included. -/
theorem cross_comp_reverseMoveHom_pair (l : List I) {i j c : I}
    (hji : j ≠ i) (hci : c ≠ i) :
    cl D Sc (l ++ [j, c] ++ [i]) (l ++ [c, j] ++ [i]) [.cross l.length]
      (sChain_crossAt l [i] j c) ≫ reverseMoveHom D Sc i l [c, j] =
    reverseMoveHom D Sc i l [j, c] ≫
      cl D Sc (l ++ i :: [j, c]) (l ++ i :: [c, j]) [.cross (l.length + 1)]
        (sChain_cross_succ l [] i j c) := by
  simp only [reverseMoveHom]
  rw [intertwinerHom_of_ne D Sc _ _ hji, intertwinerHom_of_ne D Sc _ _ hci,
    intertwinerHom_of_ne D Sc _ _ hci, intertwinerHom_of_ne D Sc _ _ hji]
  simp only [Category.assoc, eqToHom_trans_assoc]
  repeat first
    | rw [cl_comp_eqToHom_assoc]
    | rw [cl_comp_eqToHom]
    | rw [eqToHom_comp_cl_assoc]
    | rw [eqToHom_comp_cl]
    | rw [cl_comp_assoc]
    | rw [cl_comp]
  symm
  apply braid_ne_gen D Sc l [] j c i (fun h => hji h.1)
    (by simp) (by simp) <;> simp
  all_goals simp

end OddMath.QuiverHecke
