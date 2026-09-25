import OddMath.Frontier.OmissionWordControls
import OddMath.Frontier.OmissionCanonical

/-! Preproduction controls for the frozen descending-block word only. -/
namespace OddMath.Frontier.OmissionCanonicalControls
open OddMath.SkewPolynomial (SkewPolynomial)
open OmissionWord NilCoxeterWords AllRankDivided
noncomputable section

theorem word_two : (LongestDivided.wordIn 0 2 le_rfl).reverse.map Fin.rev = [0] := rfl
theorem word_three : (LongestDivided.wordIn 1 3 le_rfl).reverse.map Fin.rev = [1,0,1] := rfl
theorem word_four : (LongestDivided.wordIn 2 4 le_rfl).reverse.map Fin.rev = [2,1,0,2,1,2] := rfl

theorem n2 (b : Bool) : Trichotomy ([(0,b)] : Marked 0) := by
  cases b
  · exact Or.inr (Or.inl (by simp))
  · exact Or.inl (fun f hf => hf 0)

theorem n3_exception_omission : omission ([(1,false),(0,true),(1,false)] : Marked 1) = [1,1] := rfl

theorem n3_exception_value : hybrid ([(1,false),(0,true),(1,false)] : Marked 1)
    OmissionWordControls.e1 = -2 := by
  exact OmissionWordControls.n3_101 false true false

theorem n3_exception_nonreduced :
    ¬Reduced (omission ([(1,false),(0,true),(1,false)] : Marked 1)) := by decide

-- This covariance is on every actual polynomial, not just an elementary test.
theorem n3_tff (f : SkewPolynomial 3) :
    divided (1 : Fin 2) (s 0 (s 1 f)) = s 0 (s 1 (divided 0 f)) := by
  have h₁ := NonadjacentDivided.covariance (1 : Fin 3) 2 0 1 (by decide) (by decide) (s 1 f)
  have h₂ := NonadjacentDivided.covariance (0 : Fin 3) 2 1 2 (by decide) (by decide) f
  have a₀ := NonadjacentDivided.adjacent (0 : Fin 2)
  have a₁ := NonadjacentDivided.adjacent (1 : Fin 2)
  change NonadjacentDivided.dividedPair 0 1 _ = divided (0 : Fin 2) at a₀
  change NonadjacentDivided.dividedPair 1 2 _ = divided (1 : Fin 2) at a₁
  norm_num [Equiv.swap_apply_def, Fin.ext_iff] at h₁ h₂
  change divided (1 : Fin 2) (s 0 (s 1 f)) =
    -s 0 (NonadjacentDivided.dividedPair 0 2 _ (s 1 f)) at h₁
  change NonadjacentDivided.dividedPair 0 2 _ (s 1 f) =
    -s 1 (NonadjacentDivided.dividedPair 0 1 _ f) at h₂
  rw [h₁, h₂, a₀, map_neg, neg_neg]

theorem n3_ttf (f : SkewPolynomial 3)
    (hf : f ∈ OddSymmetricKernel.kernelSubring 1) :
    divided (1 : Fin 2) (divided 0 (s 1 f)) = 0 := by
  have h₁ := NonadjacentDivided.covariance (0 : Fin 3) 1 1 2 (by decide) (by decide) f
  have h₂ := NonadjacentDivided.covariance (1 : Fin 3) 2 1 2 (by decide) (by decide)
    (NonadjacentDivided.dividedPair 0 2 (by decide) f)
  have a₀ := NonadjacentDivided.adjacent (0 : Fin 2)
  have a₁ := NonadjacentDivided.adjacent (1 : Fin 2)
  change NonadjacentDivided.dividedPair 0 1 _ = divided (0 : Fin 2) at a₀
  change NonadjacentDivided.dividedPair 1 2 _ = divided (1 : Fin 2) at a₁
  norm_num [Equiv.swap_apply_def, Fin.ext_iff] at h₁ h₂
  rw [NonadjacentDivided.symmetric (2 : Fin 3) 1] at h₂
  rw [a₀] at h₁
  rw [a₁] at h₂
  change divided (0 : Fin 2) (s 1 f) = -s 1 (NonadjacentDivided.dividedPair 0 2 _ f) at h₁
  change divided (1 : Fin 2) (s 1 (NonadjacentDivided.dividedPair 0 2 _ f)) =
    -s 1 (divided 1 (NonadjacentDivided.dividedPair 0 2 _ f)) at h₂
  rw [h₁, map_neg, h₂, neg_neg]
  have hz := IntervalAnnihilation.annihilate_length (0 : Fin 3) 1 (by decide) f hf
  change divided (1 : Fin 2) (NonadjacentDivided.dividedPair 0 2 _ f) = 0 at hz
  rw [hz, map_zero]

theorem n3 (a b c : Bool) : Trichotomy ([(1,a),(0,b),(1,c)] : Marked 1) := by
  cases c
  · cases b
    · cases a
      · exact Or.inr (Or.inl (by simp))
      · apply Or.inl
        intro f hf
        change divided (1 : Fin 2) (s 0 (s 1 f)) = 0
        rw [n3_tff, hf 0, map_zero, map_zero]
    · cases a
      · exact Or.inr (Or.inr n3_exception_nonreduced)
      · exact Or.inl n3_ttf
  · apply Or.inl
    intro f hf
    cases a <;> cases b <;> simp [hybrid, hf 1]

-- Postproduction controls: exact exports, not new finite evidence for the theorem.
theorem actual_frozen_word (n : ℕ) : OmissionCanonical.word n =
    (LongestDivided.wordIn n (n+2) le_rfl).reverse.map Fin.rev := rfl

example (n : ℕ) : Reduced (OmissionCanonical.word n) := OmissionCanonical.word_reduced n
example (n : ℕ) : permutation (OmissionCanonical.word n) =
    LongestElementary.longest (n+2) := OmissionCanonical.word_permutation n

example (n : ℕ) (m : Marked n) (he : erase m = OmissionCanonical.word n) :
    (∀ f ∈ OddSymmetricKernel.kernelSubring n, hybrid m f = 0) ∨
      (∀ a ∈ m, a.2 = false) ∨ ¬Reduced (omission m) := OmissionCanonical.trichotomy n m he

example (n : ℕ) (f g : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    LongestDivided.applyWord (OmissionCanonical.word n) (f*g) =
      SignedPermutation.skewAction (LongestElementary.longest (n+2)) f *
        LongestDivided.applyWord (OmissionCanonical.word n) g := OmissionCanonical.left_kernel n f g hf

end
end OddMath.Frontier.OmissionCanonicalControls
