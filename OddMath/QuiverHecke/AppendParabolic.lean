/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.Parabolic
import Categorification.TypeA.NormalForm

/-!
# Input parabolic factorization for append coordinates

The permutation step of the append PBW decomposition, the mirror of
`OddMath.QuiverHecke.InputParabolic`: every `w ∈ S_{n+1}` factors uniquely as
`u⁻¹ (v × 1)` with `u` a shuffle for the block decomposition `n + 1`, and the
lengths add. The old block now consists of the first `n` strands, so its
crossing word needs no shift. See `docs/Nondegeneracy/AppendCoordinates.md`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open Categorification.TypeA Equiv

/-- Inverse shuffles index the positions of the appended strand. -/
abbrev AppendShuffle {n m : ℕ} (h : n + 1 = m) := Shuffle h

/-- The input-side permutation: old strands act first. -/
def appendPermutation {n m : ℕ} (h : n + 1 = m) (p : Perm (Fin n) × AppendShuffle h) :
    Perm (Fin m) :=
  p.2.1⁻¹ * blockPerm h p.1 1

theorem appendPermutation_bijective {n m : ℕ} (h : n + 1 = m) :
    Function.Bijective (appendPermutation h) := by
  constructor
  · rintro ⟨b, u⟩ ⟨b', u'⟩ he
    have hi := congrArg (fun w : Perm (Fin m) => w⁻¹) he
    simp only [appendPermutation, mul_inv_rev, blockPerm_inv, inv_one, inv_inv] at hi
    obtain ⟨hb, _, hu⟩ := blockPerm_mul_injective h u.2 u'.2 hi
    exact Prod.ext (inv_injective hb) (Subtype.ext hu)
  · intro w
    obtain ⟨⟨a, b, u⟩, he⟩ := (parabolicEquiv h).surjective w⁻¹
    have hb : b = 1 := Subsingleton.elim _ _
    refine ⟨(a⁻¹, u), ?_⟩
    have hi := congrArg (fun z : Perm (Fin m) => z⁻¹) he
    simpa only [parabolicEquiv_apply, hb, mul_inv_rev, blockPerm_inv, inv_one,
      inv_inv, appendPermutation] using hi

/-- The input factorization has no cancellation of crossings. -/
theorem length_appendPermutation {n m : ℕ} (h : n + 1 = m)
    (p : Perm (Fin n) × AppendShuffle h) :
    length m (appendPermutation h p) = length n p.1 + length m p.2.1 := by
  have hl := length_blockPerm_mul h p.1⁻¹ (1 : Perm (Fin 1)) p.2.2
  rw [← length_inv (blockPerm h p.1⁻¹ 1 * p.2.1)] at hl
  simpa only [mul_inv_rev, blockPerm_inv, inv_one, inv_inv, length_inv,
    length_one, add_zero, appendPermutation] using hl

/-- Algebraic word order; `cw` executes the right-hand old block first. -/
def appendCrossingWord {n m : ℕ} (h : n + 1 = m) (p : Perm (Fin n) × AppendShuffle h) :
    List ℕ :=
  canWord m p.2.1⁻¹ ++ canWord n p.1

/-- Reduced concatenation for the input-side PBW leading term. -/
theorem appendCrossingWord_spec {n m : ℕ} (h : n + 1 = m)
    (p : Perm (Fin n) × AppendShuffle h) :
    IsReduced m (appendCrossingWord h p) ∧
      wordProd m (appendCrossingWord h p) = appendPermutation h p := by
  have hs : wordProd m (canWord n p.1) =
      blockPerm h p.1 1 := by
    simpa only [shiftWord, List.map_nil, List.append_nil, wordProd_nil, wordProd_canWord] using
      wordProd_append_shiftWord h (validWord_canWord n p.1)
        (show ValidWord 1 [] from by simp [ValidWord])
  have hw : wordProd m (appendCrossingWord h p) = appendPermutation h p := by
    rw [appendCrossingWord, wordProd_append, wordProd_canWord, hs]
    rfl
  refine ⟨⟨validWord_append.mpr ⟨validWord_canWord _ _,
    (validWord_canWord n p.1).of_le (by omega)⟩, ?_⟩, hw⟩
  rw [hw, length_appendPermutation]
  simp only [appendCrossingWord, List.length_append, length_canWord, length_inv, Nat.add_comm]

end OddMath.QuiverHecke
