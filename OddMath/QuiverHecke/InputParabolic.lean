/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.Parabolic
import Categorification.TypeA.NormalForm

/-!
# Input parabolic factorization for prepend coordinates

The permutation step of the prepend PBW decomposition: invert the output
parabolic factorization, without introducing a reflection of diagrams.
The right factor acts on the old input strands. The corresponding Hom-algebra
coordinate construction is described in `docs/Nondegeneracy/PrependCoordinates.md`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open Categorification.TypeA Equiv

/-- Inverse shuffles index the positions of the prepended strand. -/
abbrev PrependShuffle (n : ℕ) := Shuffle (Nat.add_comm 1 n)

/-- The input-side permutation: old strands act first. -/
def prependPermutation (n : ℕ) (p : Perm (Fin n) × PrependShuffle n) :
    Perm (Fin (n + 1)) :=
  p.2.1⁻¹ * blockPerm (Nat.add_comm 1 n) 1 p.1

theorem prependPermutation_bijective (n : ℕ) : Function.Bijective (prependPermutation n) := by
  constructor
  · rintro ⟨b, u⟩ ⟨b', u'⟩ he
    have hi := congrArg (fun w : Perm (Fin (n + 1)) => w⁻¹) he
    simp only [prependPermutation, mul_inv_rev, blockPerm_inv, inv_one, inv_inv] at hi
    obtain ⟨_, hb, hu⟩ := blockPerm_mul_injective (Nat.add_comm 1 n) u.2 u'.2 hi
    exact Prod.ext (inv_injective hb) (Subtype.ext hu)
  · intro w
    obtain ⟨⟨a, b, u⟩, he⟩ := (parabolicEquiv (Nat.add_comm 1 n)).surjective w⁻¹
    have ha : a = 1 := Subsingleton.elim _ _
    refine ⟨(b⁻¹, u), ?_⟩
    have hi := congrArg (fun z : Perm (Fin (n + 1)) => z⁻¹) he
    simpa only [parabolicEquiv_apply, ha, mul_inv_rev, blockPerm_inv, inv_one,
      inv_inv, prependPermutation] using hi

/-- Unique old-input permutation and inverse-shuffle coordinates, at every height. -/
def prependPermutationEquiv (n : ℕ) :
    Perm (Fin n) × PrependShuffle n ≃ Perm (Fin (n + 1)) :=
  Equiv.ofBijective (prependPermutation n) (prependPermutation_bijective n)

@[simp] theorem prependPermutationEquiv_apply (n : ℕ)
    (p : Perm (Fin n) × PrependShuffle n) :
    prependPermutationEquiv n p = p.2.1⁻¹ * blockPerm (Nat.add_comm 1 n) 1 p.1 := rfl

/-- The input factorization has no cancellation of crossings. -/
theorem length_prependPermutation (n : ℕ) (p : Perm (Fin n) × PrependShuffle n) :
    length (n + 1) (prependPermutation n p) = length n p.1 + length (n + 1) p.2.1 := by
  have h := length_blockPerm_mul (Nat.add_comm 1 n) (1 : Perm (Fin 1)) p.1⁻¹ p.2.2
  rw [← length_inv (blockPerm (Nat.add_comm 1 n) 1 p.1⁻¹ * p.2.1)] at h
  simpa only [mul_inv_rev, blockPerm_inv, inv_one, inv_inv, length_inv,
    length_one, zero_add, prependPermutation] using h

/-- Algebraic word order; `cw` executes the right-hand old block first. -/
def prependCrossingWord (n : ℕ) (p : Perm (Fin n) × PrependShuffle n) : List ℕ :=
  canWord (n + 1) p.2.1⁻¹ ++ shiftWord 1 (canWord n p.1)

/-- Reduced concatenation for the input-side PBW leading term. -/
theorem prependCrossingWord_spec (n : ℕ) (p : Perm (Fin n) × PrependShuffle n) :
    IsReduced (n + 1) (prependCrossingWord n p) ∧
      wordProd (n + 1) (prependCrossingWord n p) = prependPermutation n p := by
  have hs : wordProd (n + 1) (shiftWord 1 (canWord n p.1)) =
      blockPerm (Nat.add_comm 1 n) 1 p.1 := by
    simpa only [List.nil_append, wordProd_nil, wordProd_canWord] using
      wordProd_append_shiftWord (Nat.add_comm 1 n)
        (show ValidWord 1 [] from by simp [ValidWord]) (validWord_canWord n p.1)
  have hw : wordProd (n + 1) (prependCrossingWord n p) = prependPermutation n p := by
    rw [prependCrossingWord, wordProd_append, wordProd_canWord, hs]
    rfl
  refine ⟨⟨validWord_append.mpr ⟨validWord_canWord _ _,
    (validWord_canWord n p.1).shiftWord (Nat.add_comm 1 n)⟩, ?_⟩, hw⟩
  rw [hw, length_prependPermutation]
  simp only [prependCrossingWord, List.length_append, length_canWord, length_shiftWord,
    length_inv, Nat.add_comm]

end OddMath.QuiverHecke
