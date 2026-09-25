import OddMath.Frontier.OddPlactic
import OddMath.Frontier.PbwRealization

/-!
# The source plactic-to-skew quotient map

Ellis, arXiv:1111.3932v1, §3.1 (3.1)–(3.2) and the intermediate
quotient display: the letter with paper label i+1 maps to (-1)^i x_i.
Both signed Knuth families retain their weak endpoints. Surjectivity uses
ordered-word realization in the actual skew model, not a tableau basis,
quotient normal forms, or PBW injectivity. Coefficients remain integers.
-/

namespace OddMath.Frontier.PlacticEvaluation

open OddMath.SkewPolynomial

/-- Source tilde normalization; the paper's label is `i.val + 1`. -/
noncomputable def tildeGenerator {n : ℕ} (i : Fin n) : SkewPolynomial n :=
  (-1 : ℤ) ^ i.val • generator i

/-- Integer sign changes preserve off-diagonal anticommutation. -/
theorem tilde_anticommute {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    tildeGenerator i * tildeGenerator j = -(tildeGenerator j * tildeGenerator i) := by
  have hg : generator i * generator j = -(generator j * generator i) :=
    OddMath.PbwL1.rel_anticommute i j h
  simp only [tildeGenerator, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hg, smul_neg, mul_comm ((-1 : ℤ) ^ i.val)]

/-- Exact source K′ and K′′, with the allowed repeated-letter endpoints. -/
theorem respectsKnuth (n : ℕ) : OddPlactic.RespectsKnuth (tildeGenerator (n := n)) := by
  constructor
  · intro x y z hxy hyz
    have hxz : x < z := lt_of_lt_of_le hxy hyz
    rw [_root_.mul_assoc, tilde_anticommute z x (ne_of_gt hxz), mul_neg,
      ← _root_.mul_assoc]
  · intro x y z hxy hyz
    have hxz : x < z := lt_of_le_of_lt hxy hyz
    rw [tilde_anticommute x z (ne_of_lt hxz), neg_mul]

/-- The actual source quotient map, factored by the proved Knuth laws. -/
noncomputable def toSkew (n : ℕ) : OddPlactic.Plactic n →+* SkewPolynomial n :=
  OddPlactic.lift tildeGenerator (respectsKnuth n)

@[simp] theorem toSkew_q (n : ℕ) (i : Fin n) :
    toSkew n (OddPlactic.q n i) = tildeGenerator i :=
  OddPlactic.lift_q _ _ i

/-- Literal left-to-right evaluation for every word, including repetitions. -/
theorem toSkew_word (n : ℕ) (w : List (Fin n)) :
    toSkew n (OddPlactic.word n w) = (w.map tildeGenerator).prod :=
  OddPlactic.lift_word _ _ w

/-- The sign is its own inverse, so every untilded generator is in the image. -/
theorem toSkew_signed_q (n : ℕ) (i : Fin n) :
    toSkew n ((-1 : ℤ) ^ i.val • OddPlactic.q n i) = generator i := by
  rw [map_zsmul, toSkew_q, tildeGenerator, smul_smul, ← mul_pow]
  norm_num

/-- A sign-corrected word in the genuine plactic ring. No sorting is asserted. -/
def untildedWord {n : ℕ} (w : List (Fin n)) : OddPlactic.Plactic n :=
  (w.map (fun i => (-1 : ℤ) ^ i.val • OddPlactic.q n i)).prod

/-- Connect literal plactic words to the already checked PBW realization map. -/
theorem toSkew_untildedWord {n : ℕ} (w : List (Fin n)) :
    toSkew n (untildedWord w) = OddMath.PbwL3.Phi n (PbwRealization.word w) := by
  induction w with
  | nil => simp [untildedWord, PbwRealization.word]
  | cons i w ih =>
    change toSkew n (((-1 : ℤ) ^ i.val • OddPlactic.q n i) * untildedWord w) =
      OddMath.PbwL3.Phi n (OddMath.PbwL2.q n i * PbwRealization.word w)
    rw [map_mul, map_mul, toSkew_signed_q, OddMath.PbwL3.Phi_q, ih]

/-- Every integer monomial has an explicit plactic preimage. -/
theorem toSkew_monomial (n : ℕ) (a : Fin n → ℕ) (c : ℤ) :
    toSkew n (c • untildedWord (PbwRealization.orderedList a)) = monomial a c := by
  rw [map_zsmul, toSkew_untildedWord, ← map_zsmul]
  exact PbwRealization.Phi_smul_word a c

/-- Surjectivity on arbitrary integer skew polynomials in every finite rank.
This neither assumes nor proves injectivity, nor uses a tableau-basis claim. -/
theorem toSkew_surjective (n : ℕ) : Function.Surjective (toSkew n) := by
  intro f
  induction f using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add f g hf hg =>
    obtain ⟨x, hx⟩ := hf
    obtain ⟨y, hy⟩ := hg
    exact ⟨x + y, by rw [map_add, hx, hy]⟩
  | single a c =>
    exact ⟨c • untildedWord (PbwRealization.orderedList a), toSkew_monomial n a c⟩

end OddMath.Frontier.PlacticEvaluation
