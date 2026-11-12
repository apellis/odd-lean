/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSupport
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedAppendTransform

/-! # Positive-degree nilpotence in the truncated ELV category

`truncatedContent_positive_pow_zero` derives a common exponent for all positive
integer-degree endomorphisms of every word of a fixed content. It supplies the
quotient-level nilpotence needed for the reservoir post-dot in the coefficient
construction. Integer degree, not super parity, controls the exponent. The
coefficient algebra retains its exterior multiplication.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ)

/-- The bound is derived from the coefficient bound and the cyclotomic append
recurrence. It is uniform in the word, positive degree, and endomorphism. -/
theorem truncatedContent_positive_pow_zero_of_bound (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (ν : List I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (v : List I), v.Perm ν → ∀ (d : ℤ), 0 < d →
      ∀ f : TruncatedEnd D Sc cutoff N v,
        f ∈ truncatedEndDegree D Sc cutoff N sy hc v d → f ^ e = 0 := by
  classical
  choose B hB using fun v : List I =>
    truncatedContent_bounded_of_bound D Sc cutoff sy hc N M hM hbound v v
  let K := ν.permutations.toFinset.sup B
  refine ⟨K + 1, by omega, ?_⟩
  intro v hv d hd f hf
  have hv' : v ∈ ν.permutations.toFinset := by simpa using hv
  have hb : B v ≤ K := Finset.le_sup hv'
  have hp := SetLike.pow_mem_graded (K + 1) hf
  have hdeg : (B v : ℤ) < (K + 1) • d := by
    rw [nsmul_eq_mul]
    have hcast : (B v : ℤ) ≤ K := by exact_mod_cast hb
    have hk : (0 : ℤ) ≤ K := Nat.cast_nonneg K
    push_cast
    nlinarith
  change f ^ (K + 1) ∈ truncatedDegree D Sc cutoff sy hc N v v ((K + 1) • d) at hp
  rw [hB v _ (Or.inr hdeg)] at hp
  exact hp

/-- For finite colours every fixed content has a uniform positive-degree
nilpotence exponent, over any commutative ground ring (including the zero ring). -/
theorem truncatedContent_positive_pow_zero [Finite I] (ν : List I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (v : List I), v.Perm ν → ∀ (d : ℤ), 0 < d →
      ∀ f : TruncatedEnd D Sc cutoff N v,
        f ∈ truncatedEndDegree D Sc cutoff N sy hc v d → f ^ e = 0 := by
  obtain ⟨M, hM, hb⟩ := SKM.SYM.exists_coefficientDegree_bound D sy
  exact truncatedContent_positive_pow_zero_of_bound D Sc cutoff sy hc N M hM hb ν

/-- The positioned affine dot in the coefficient-truncated quotient. -/
def truncatedDot (v : List I) (r : ℕ) : TruncatedEnd D Sc cutoff N v :=
  (truncatedIdeal D Sc cutoff N v v).mkQ
    ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] dotE D Sc v r)

include sy hc in
/-- The last-strand dot of the existing append transformation is nilpotent,
uniformly on the source content. This is componentwise, not a claim of one
exponent on the unbounded category of all words. -/
theorem truncatedAppendDot_pow_zero [Finite I] (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ v : TruncatedCategory D Sc cutoff N, v.word.Perm ν →
      let f : TruncatedEnd D Sc cutoff N (v.word ++ [i]) :=
        (truncatedAppendDot D Sc cutoff N i).app (D.parity i) v
      f ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := truncatedContent_positive_pow_zero D Sc cutoff sy hc N (ν ++ [i])
  refine ⟨e, he, fun v hv => hp _ (hv.append (List.Perm.refl _)) _ ?_ _
    (truncatedAppendDot_degree D Sc cutoff N sy hc i v)⟩
  have := sy.pos i
  omega

/-- Nilpotence of the appended last-strand dot, with one exponent for each source content and
appended colour. This is the only input on the parameters that the content-induction and
reservoir dot nilpotence results use. -/
structure TruncatedAppendDotNilpotent : Prop where
  /-- For each source content `ν` and appended colour `i`, one positive exponent kills the
  appended dot on every word of content `ν`. -/
  out : ∀ (ν : List I) (i : I), ∃ e : ℕ, 0 < e ∧ ∀ v : TruncatedCategory D Sc cutoff N,
    v.word.Perm ν →
      let f : TruncatedEnd D Sc cutoff N (v.word ++ [i]) :=
        (truncatedAppendDot D Sc cutoff N i).app (D.parity i) v
      f ^ e = 0

include sy hc in
/-- Homogeneous parameters give nilpotence of the appended dot. -/
theorem truncatedAppendDotNilpotent [Finite I] : TruncatedAppendDotNilpotent D Sc cutoff N :=
  ⟨truncatedAppendDot_pow_zero D Sc cutoff sy hc N⟩

end OddMath.QuiverHecke.ELVOld
