/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Logic.Equiv.Fin.Basic
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.CapWindows

/-! # The auxiliary probe maps of nonnegative heights

Case (a) of §3 of `docs/Nondegeneracy/ProbeWindowInverse.md`: for `k ≥ 0` and `H = h - k ≥ 0`
the auxiliary map `M : X ⟶ Y ⊕ F ⊕ R` with rows `s`, `v_t = xᵗ ≫ v` (`t < H`) and
`c_r • v_{-r-1}` (`r < k`, `c_r = q^(r+1)`) is invertible whenever the cap window
`[s; v₀, …, v_{h-1}]` is (`ProbeWindow.exists_isCapInverse_caseA`, (7) there). Its rows are
those of the shifted window `F_k` of (5), reordered and multiplied by the units `c_r`
(`ProbeWindow.IsCapInverse.reindex`).

Dually, case (d) (`k < 0`, `H < 0`, (14) there): the auxiliary map `X ⊕ Z ⊕ G ⟶ Y` is the
shifted cup window `P_a` of (6) with its columns reordered and multiplied by the units
`d_s = q^(s+2)` and `-1` (`ProbeWindow.exists_isCupInverse_caseD`).
-/

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

open CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] {X Y O : C}

/-- Reordering the rows of a cap window and multiplying them by units `c m` with
`c m * c m = 1` preserves entrywise inverses (the inverse columns are reordered and multiplied
by the same units). -/
theorem IsCapInverse.reindex {h h' : ℕ} {s : X ⟶ Y} {w : Fin h → (X ⟶ O)} {j : Y ⟶ X}
    {A : Fin h → (O ⟶ X)} (H : IsCapInverse s w j A) (e : Fin h' ≃ Fin h) (c : Fin h' → ℤ)
    (hc : ∀ m, c m * c m = 1) :
    IsCapInverse s (fun m => c m • w (e m)) j (fun m => c m • A (e m)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨h1, fun n => ?_, fun m => ?_, fun n m => ?_, ?_⟩
  · rw [Preadditive.zsmul_comp, h2, smul_zero]
  · rw [Preadditive.comp_zsmul, h3, smul_zero]
  · rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, h4]
    by_cases hnm : n = m
    · subst hnm; simp only [↓reduceIte, hc, one_smul]
    · have : ¬ e n = e m := fun h => hnm (e.injective h)
      simp only [this, hnm, ↓reduceIte, smul_zero]
  · rw [← h5, ← e.sum_comp (fun n => w n ≫ A n)]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, hc, one_smul]

/-- The reordering of the shifted window `F_k` (slots `n - k`, `n < H + k`) into the rows of
the auxiliary map of case (a): slot `t` (`t < H`) first, then slot `-r-1` (`r < k`). -/
def caseAPerm (H k : ℕ) : Fin (H + k) ≃ Fin (H + k) :=
  ((finAddFlip (m := H) (n := k)).trans (finSumFinEquiv.symm.trans
    ((Equiv.sumCongr Fin.revPerm (Equiv.refl _)).trans finSumFinEquiv))).trans
    (finCongr (Nat.add_comm k H))

lemma caseAPerm_castAdd (H k : ℕ) (t : Fin H) :
    ((caseAPerm H k (Fin.castAdd k t) : Fin (H + k)) : ℕ) = t + k := by
  simp [caseAPerm, Nat.add_comm]

lemma caseAPerm_natAdd (H k : ℕ) (r : Fin k) :
    ((caseAPerm H k (Fin.natAdd H r) : Fin (H + k)) : ℕ) = k - (r + 1) := by
  simp [caseAPerm]

/-- **Case (a)**, (7) of `ProbeWindowInverse.md`: for `k ≥ 0`, `H ≥ 0`, if the cap window
`[s; xⁿ ≫ v]_{n < H + k}` is invertible, so is the auxiliary map with rows `s`,
`xᵗ ≫ v` (`t < H`) and `q^(r+1) • (x^{-r-1} ≫ v)` (`r < k`). -/
theorem exists_isCapInverse_caseA (s : X ⟶ Y) (x : Aut X) (y : Aut Y) (v : X ⟶ O)
    (u : O ⟶ Y) (q : ℤ) (hq : q * q = 1) (hslide : s ≫ y.hom - q • (x.hom ≫ s) = v ≫ u)
    {H k : ℕ} (h0 : ∃ j A, IsCapInverse s (fun n : Fin (H + k) => (x ^ (n : ℤ)).hom ≫ v) j A) :
    ∃ j A, IsCapInverse s
      (Fin.append (fun t : Fin H => (x ^ (t : ℤ)).hom ≫ v)
        (fun r : Fin k => q ^ ((r : ℕ) + 1) • ((x ^ (-(r : ℤ) - 1)).hom ≫ v))) j A := by
  obtain ⟨j, A, hjA⟩ := exists_isCapInverse_shift s x y v u q hq hslide
    (Nat.le_add_left k H) h0
  let c : Fin (H + k) → ℤ := Fin.append (fun _ : Fin H => 1) (fun r : Fin k => q ^ ((r : ℕ) + 1))
  have hc : ∀ m, c m * c m = 1 := fun m => by
    refine Fin.addCases (fun t => ?_) (fun r => ?_) m
    · simp [c]
    · simp only [c, Fin.append_right]; rw [← mul_pow, hq, one_pow]
  refine ⟨j, fun m => c m • A (caseAPerm H k m), ?_⟩
  convert hjA.reindex (caseAPerm H k) c hc using 1
  funext m
  refine Fin.addCases (fun t => ?_) (fun r => ?_) m
  · simp only [Fin.append_left, c, one_smul]
    congr 3
    rw [caseAPerm_castAdd]; push_cast; ring
  · simp only [Fin.append_right, c]
    congr 4
    rw [caseAPerm_natAdd]
    have := r.isLt
    push_cast [Nat.cast_sub (show (r : ℕ) + 1 ≤ k by omega)]
    ring

/-- Reordering the columns of a cup window and multiplying them by units preserves entrywise
inverses. -/
theorem IsCupInverse.reindex {h h' : ℕ} {s : X ⟶ Y} {w : Fin h → (O ⟶ Y)} {j : Y ⟶ X}
    {D : Fin h → (Y ⟶ O)} (H : IsCupInverse s w j D) (e : Fin h' ≃ Fin h) (c : Fin h' → ℤ)
    (hc : ∀ m, c m * c m = 1) :
    IsCupInverse s (fun m => c m • w (e m)) j (fun m => c m • D (e m)) := by
  rw [isCupInverse_iff_op] at H ⊢
  simpa only [op_zsmul] using H.reindex e c hc

/-- The reordering of the shifted cup window `P_a` (slots `n - a`, `n < a + g`) into the columns
of the auxiliary map of case (d): slot `-s-1` (`s < a`) first, then slot `t` (`t < g`). -/
def caseDPerm (a g : ℕ) : Fin (a + g) ≃ Fin (a + g) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr Fin.revPerm (Equiv.refl _)).trans finSumFinEquiv)

lemma caseDPerm_castAdd (a g : ℕ) (r : Fin a) :
    ((caseDPerm a g (Fin.castAdd g r) : Fin (a + g)) : ℕ) = a - (r + 1) := by
  simp [caseDPerm]

lemma caseDPerm_natAdd (a g : ℕ) (t : Fin g) :
    ((caseDPerm a g (Fin.natAdd a t) : Fin (a + g)) : ℕ) = a + t := by
  simp [caseDPerm]

/-- **Case (d)**, (14) of `ProbeWindowInverse.md`: for `k = -a < 0` and `h = -(a + g) < 0`, if
the cup window `[s, u ≫ yⁿ]_{n < a + g}` is invertible, so is the auxiliary map
`X ⊕ Oᵃ ⊕ Oᵍ ⟶ Y` with columns `s`, `q^(r+2) • (u ≫ y^{-r-1})` (`r < a`) and `-(u ≫ yᵗ)`
(`t < g`). -/
theorem exists_isCupInverse_caseD (s : X ⟶ Y) (x : Aut X) (y : Aut Y) (v : X ⟶ O)
    (u : O ⟶ Y) (q : ℤ) (hq : q * q = 1) (hslide : s ≫ y.hom - q • (x.hom ≫ s) = v ≫ u)
    {a g : ℕ} (h0 : ∃ j D, IsCupInverse s (fun n : Fin (a + g) => u ≫ (y ^ (n : ℤ)).hom) j D) :
    ∃ j D, IsCupInverse s
      (Fin.append (fun r : Fin a => q ^ ((r : ℕ) + 2) • (u ≫ (y ^ (-(r : ℤ) - 1)).hom))
        (fun t : Fin g => (-1 : ℤ) • (u ≫ (y ^ (t : ℤ)).hom))) j D := by
  obtain ⟨j, D, hjD⟩ := exists_isCupInverse_shift s x y v u q hq hslide
    (Nat.le_add_right a g) h0
  let c : Fin (a + g) → ℤ :=
    Fin.append (fun r : Fin a => q ^ ((r : ℕ) + 2)) (fun _ : Fin g => -1)
  have hc : ∀ m, c m * c m = 1 := fun m => by
    refine Fin.addCases (fun r => ?_) (fun t => ?_) m
    · simp only [c, Fin.append_left]; rw [← mul_pow, hq, one_pow]
    · simp [c]
  refine ⟨j, fun m => c m • D (caseDPerm a g m), ?_⟩
  convert hjD.reindex (caseDPerm a g) c hc using 1
  funext m
  refine Fin.addCases (fun r => ?_) (fun t => ?_) m
  · simp only [Fin.append_left, c]
    congr 4
    rw [caseDPerm_castAdd]
    have := r.isLt
    push_cast [Nat.cast_sub (show (r : ℕ) + 1 ≤ a by omega)]
    ring
  · simp only [Fin.append_right, c]
    congr 4
    rw [caseDPerm_natAdd]; push_cast; ring

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
