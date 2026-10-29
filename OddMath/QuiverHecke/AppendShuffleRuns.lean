/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.AppendParabolic

/-!
# Append shuffles are ascending runs

For the block decomposition `n + 1`, a shuffle `u` is determined by the position
`j = u⁻¹(n)` of the appended strand, and `u⁻¹ = s_j s_(j+1) ⋯ s_(n-1)`. Its canonical
reduced word is the ascending run `[j, j+1, …, n-1]` (`canWord_runPerm`), so the moving
crossings of the append PBW basis first cross the last two strands and then move along
the old strands only. `appendRunEquiv : Fin (n + 1) ≃ AppendShuffle h` reindexes the
shuffles by `j`. This is the permutation input of the left-oriented correction (2) of
`docs/Nondegeneracy/AppendCoordinates.md` §4.
-/

noncomputable section
namespace OddMath.QuiverHecke
open Categorification.TypeA Equiv

/-- The code whose word is the ascending run `[j, …, n-1]`. -/
def runCode (j : ℕ) : ℕ → List ℕ
  | 0 => []
  | t + 1 => (if j ≤ t then t else t + 1) :: runCode j t

@[simp] theorem length_runCode (j t : ℕ) : (runCode j t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [runCode, ih]

theorem isCode_runCode (j t : ℕ) : IsCode (runCode j t) := by
  induction t with
  | zero => trivial
  | succ t ih => exact ⟨by simp only [length_runCode]; split <;> omega, ih⟩

theorem codeWord_runCode (j t : ℕ) : codeWord (runCode j t) = List.range' j (t - j) := by
  induction t with
  | zero => simp [runCode]
  | succ t ih =>
    rw [runCode, codeWord_cons, ih, length_runCode]
    split
    · rename_i h
      rw [show t + 1 - t = 1 by omega, descRun_one, show t + 1 - j = (t - j) + 1 by omega,
        List.range'_concat]
      congr 2
      omega
    · rename_i h
      rw [show t + 1 - (t + 1) = 0 by omega, show t - j = 0 by omega,
        show t + 1 - j = 0 by omega]
      rfl

/-- The inverse shuffle `s_j s_(j+1) ⋯ s_(n-1)` moving position `n` to `j`. -/
def runPerm (n j : ℕ) : Perm (Fin (n + 1)) := wordProd (n + 1) (List.range' j (n - j))

theorem canWord_runPerm (n j : ℕ) :
    canWord (n + 1) (runPerm n j) = List.range' j (n - j) := by
  rw [runPerm, ← codeWord_runCode, canWord_wordProd_codeWord (isCode_runCode j n)
    (by simp)]

theorem runPerm_succ {n j : ℕ} (hj : j < n) :
    runPerm n j = sadj (n + 1) j * runPerm n (j + 1) := by
  rw [runPerm, runPerm, show n - j = (n - (j + 1)) + 1 by omega, List.range'_succ,
    wordProd_cons]

theorem runPerm_val (n j : ℕ) (hj : j ≤ n) (x : Fin (n + 1)) :
    (runPerm n j x : ℕ) =
      if (x : ℕ) < j then (x : ℕ) else if (x : ℕ) < n then (x : ℕ) + 1 else j := by
  generalize hk : n - j = k
  induction k generalizing j with
  | zero =>
    obtain rfl : j = n := by omega
    simp only [runPerm, Nat.sub_self, List.range'_zero, wordProd, List.map_nil,
      List.prod_nil, Perm.one_apply]
    have := x.2
    split_ifs <;> omega
  | succ k ih =>
    rw [runPerm_succ (by omega), Perm.mul_apply, sadj_val, ih (j + 1) (by omega) (by omega)]
    have := x.2
    unfold swapNat
    split_ifs <;> omega

theorem runPerm_last (n j : ℕ) (hj : j ≤ n) : (runPerm n j (Fin.last n) : ℕ) = j := by
  rw [runPerm_val n j hj]; simp; omega

/-- The shuffle whose inverse is `runPerm n j`. -/
def appendRun (n : ℕ) (j : Fin (n + 1)) : AppendShuffle (show n + 1 = n + 1 from rfl) :=
  ⟨(runPerm n j)⁻¹, by
    refine ⟨fun x x' hx => ?_, fun y y' hy => absurd hy (by simp [Subsingleton.elim y y'])⟩
    simp only [inv_inv]
    rw [Fin.lt_def, runPerm_val n j (by omega), runPerm_val n j (by omega)]
    simp only [blockEquiv_inl_val]
    have := x.2; have := x'.2; have : (x : ℕ) < x' := hx
    split_ifs <;> omega⟩

@[simp] theorem appendRun_inv (n : ℕ) (j : Fin (n + 1)) :
    (appendRun n j).1⁻¹ = runPerm n j := inv_inv _

theorem canWord_appendRun (n : ℕ) (j : Fin (n + 1)) :
    canWord (n + 1) (appendRun n j).1⁻¹ = List.range' j (n - j) := by
  rw [appendRun_inv, canWord_runPerm]

theorem appendRun_injective (n : ℕ) : Function.Injective (appendRun n) := by
  intro j j' h
  have h' := congrArg (fun u : AppendShuffle (show n + 1 = n + 1 from rfl) =>
    ((u.1⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ)) h
  simp only [appendRun_inv, runPerm_last n _ (Nat.lt_succ_iff.mp j.2),
    runPerm_last n _ (Nat.lt_succ_iff.mp j'.2)] at h'
  exact Fin.ext h'

open scoped Classical in
theorem card_appendShuffle (n : ℕ) :
    Fintype.card (AppendShuffle (show n + 1 = n + 1 from rfl)) = n + 1 := by
  have h := Fintype.card_congr (Equiv.ofBijective _
    (appendPermutation_bijective (show n + 1 = n + 1 from rfl)))
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_fin,
    Fintype.card_fin, Nat.factorial_succ, mul_comm] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos n) h

open scoped Classical in
/-- Append shuffles are indexed by the final position of the appended strand. -/
def appendRunEquiv (n : ℕ) : Fin (n + 1) ≃ AppendShuffle (show n + 1 = n + 1 from rfl) :=
  Equiv.ofBijective (appendRun n) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨appendRun_injective n, by rw [Fintype.card_fin, card_appendShuffle]⟩)

@[simp] theorem appendRunEquiv_apply (n : ℕ) (j : Fin (n + 1)) :
    appendRunEquiv n j = appendRun n j := rfl

/-- Every append shuffle has the ascending run as canonical inverse word. -/
theorem exists_canWord_eq_range' (n : ℕ) (u : AppendShuffle (show n + 1 = n + 1 from rfl)) :
    ∃ j : Fin (n + 1), canWord (n + 1) u.1⁻¹ = List.range' j (n - j) := by
  obtain ⟨j, rfl⟩ := (appendRunEquiv n).surjective u
  exact ⟨j, canWord_appendRun n j⟩

end OddMath.QuiverHecke
