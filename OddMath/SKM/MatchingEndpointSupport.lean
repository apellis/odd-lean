/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.MixedDotGrading
import OddMath.CoveringQuantum.UDot.MixedAdjointCoefficients

/-! Endpoint support for the mismatch cases in BE2 v2 Theorem 10.3 Claims 2–3. -/
noncomputable section

namespace OddMath.SKM
variable {I X : Type*} [AddCommGroup X] (D : Datum I X)

/-- A matching preserves endpoint weight, with no independence condition on roots. -/
theorem IsMatching₂.wt_eq (μ : X) {a b : List (Letter I)}
    {R : List (StringDiagrams.Chord.TMove (Letter I))} (h : IsMatching₂ a b R) :
    wt D μ a = wt D μ b :=
  XChain.wt_eq μ (matching_bent_spec h).2.2.2.1

/-- Endpoint mismatch excludes every matching, not just reduced representatives. -/
theorem not_isMatching₂_of_weight_ne (μ : X) {a b : List (Letter I)}
    (h : wt D μ a ≠ wt D μ b) (R : List (StringDiagrams.Chord.TMove (Letter I))) :
    ¬ IsMatching₂ a b R := fun hR => h (hR.wt_eq D μ)

/-- Any family of matching representatives is empty off endpoint support. -/
theorem matching_family_eq_empty_of_weight_ne (μ : X) {a b : List (Letter I)}
    (M : Set (List (StringDiagrams.Chord.TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ a b R) (h : wt D μ a ≠ wt D μ b) : M = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro R hR
  exact not_isMatching₂_of_weight_ne D μ h R (hM R hR)
/-- Every finite fibre sum on the existing strand-labelled matching index vanishes
when the endpoints disagree; this applies to its degree fibres and parity weights. -/
theorem matching_labelled_finite_sum_eq_zero_of_weight_ne
    (μ : X) {a b : List (Letter I)}
    (M : Set (List (StringDiagrams.Chord.TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ a b R) (h : wt D μ a ≠ wt D μ b)
    {K : Type*} [AddCommMonoid K]
    (S : Finset (Σ R : {R // R ∈ M}, MatchingStrand a R.val → ℕ))
    (f : (Σ R : {R // R ∈ M}, MatchingStrand a R.val → ℕ) → K) :
    ∑ t ∈ S, f t = 0 := by
  apply Finset.sum_eq_zero
  intro t _
  exact False.elim (h ((hM t.1.val t.1.property).wt_eq D μ))
end OddMath.SKM

namespace OddMath.CoveringQuantum.UDot.GenericVerma.MixedGram
open Coefficients
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  (D : RootDatum I X)

/-- The mixed word lies in its actual modified-algebra block. -/
theorem algebraWord_mem_block (μ : X) (a : List (Bool × I)) :
    (algebraWord D μ a).val ∈ block D Coefficients.q pi (μ + shift D a) μ := by
  induction a with
  | nil =>
    simpa only [algebraWord, shift, add_zero] using
      (show one D Coefficients.q pi μ ∈ block D Coefficients.q pi μ μ from
        ⟨one_mul_one_self D Coefficients.q pi μ, one_mul_one_self D Coefficients.q pi μ⟩)
  | cons g a ih =>
    have h := mul_mem_block D Coefficients.q pi
      (halfGen_mem_block D Coefficients.q pi g.1 g.2 (μ + shift D a)) ih
    simpa only [algebraWord, shift, NonUnitalSubalgebra.coe_mul,
      add_left_comm, add_comm, add_assoc] using h
end OddMath.CoveringQuantum.UDot.GenericVerma.MixedGram

namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients GenericVerma.MixedGram
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  (D : RootDatum I X)

/-- Distinct physical endpoints force the existing mixed-word form to vanish. -/
theorem sesquilinearForm_mixed_eq_zero_of_weight_ne (μ : X) (a b : List (Bool × I))
    (h : OddMath.SKM.wt D.toSKM μ a ≠ OddMath.SKM.wt D.toSKM μ b) :
    sesquilinearForm D (algebraWord D μ a) (algebraWord D μ b) = 0 := by
  apply sesquilinearForm_orthogonal D (μ + shift D a) μ (μ + shift D b) μ
    _ _ (algebraWord_mem_block D μ a) (algebraWord_mem_block D μ b)
  exact Or.inl (by simpa only [mixed_word_physical_weight] using h)
/-- Both algebraic sides of Claim 2 vanish off its endpoint support. -/
theorem sesquilinearForm_mixed_up_leftCons_mismatch (μ : X) (i : I)
    (a b : List (Bool × I))
    (h : OddMath.SKM.wt D.toSKM μ b ≠ OddMath.SKM.wt D.toSKM μ a + D.α i) :
    sesquilinearForm D (algebraWord D μ ((true, i) :: a)) (algebraWord D μ b) = 0 ∧
    sesquilinearForm D (algebraWord D μ a) (algebraWord D μ ((false, i) :: b)) = 0 := by
  constructor <;> apply sesquilinearForm_mixed_eq_zero_of_weight_ne D
  · simpa only [OddMath.SKM.wt_cons, OddMath.SKM.sh, RootDatum.toSKM_α,
      ite_true, add_comm] using h.symm
  · intro he
    apply h
    simp only [OddMath.SKM.wt_cons, OddMath.SKM.sh, RootDatum.toSKM_α,
      Bool.false_eq_true, ite_false] at he
    rw [he]
    abel

/-- Both algebraic sides of Claim 3 vanish off its endpoint support. -/
theorem sesquilinearForm_mixed_down_leftCons_mismatch (μ : X) (i : I)
    (a b : List (Bool × I))
    (h : OddMath.SKM.wt D.toSKM μ b ≠ OddMath.SKM.wt D.toSKM μ a - D.α i) :
    sesquilinearForm D (algebraWord D μ ((false, i) :: a)) (algebraWord D μ b) = 0 ∧
    sesquilinearForm D (algebraWord D μ a) (algebraWord D μ ((true, i) :: b)) = 0 := by
  constructor <;> apply sesquilinearForm_mixed_eq_zero_of_weight_ne D
  · simpa only [OddMath.SKM.wt_cons, OddMath.SKM.sh, RootDatum.toSKM_α,
      Bool.false_eq_true, ite_false, sub_eq_add_neg, add_comm] using h.symm
  · intro he
    apply h
    simp only [OddMath.SKM.wt_cons, OddMath.SKM.sh, RootDatum.toSKM_α, ite_true] at he
    rw [he]
    abel
end OddMath.CoveringQuantum.UDot.GenericTensor
