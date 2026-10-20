/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.CupFamilyCoefficients
import OddMath.CoveringQuantum.UDot.MixedUpAdjointCoefficients
import OddMath.SKM.MatchingEndpointSupport

/-! # Coefficientwise right-cup equivalence

BE2, arXiv:1701.04133v2, Theorem 10.3 Claim 2, for the distinguished
point and natural strand-label choices of §8. Both finite degree fibers
and their equivalence are derived from the representative hypotheses.
The physical algebra words are not reversed. Endpoint mismatch is covered by
matching weight conservation and orthogonality of the existing form. Colours
are unrestricted, with no bar-consistency premise; additive weights and decidable
equalities remain explicit. Covering coefficients are purely even.
-/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open CoveringQuantum CoveringQuantum.UDot.GenericTensor
open CoveringQuantum.Coefficients CoveringQuantum.UDot.GenericVerma.MixedGram
open scoped BigOperators
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable {i : I} {a b : List (Letter I)}
variable {M N : Set (List (TMove (Letter I)))}
variable (hM : ∀ R ∈ M, IsMatching₂ ((true, i) :: a) b R ∧ StrictReduced₂ ((true, i) :: a) R)
variable (hN : ∀ S ∈ N, IsMatching₂ a ((false, i) :: b) S ∧ StrictReduced₂ a S)
variable (q : {R // R ∈ M} → ℕ → ℕ × ℕ)
variable (r : {S // S ∈ N} → ℕ → ℕ × ℕ)
variable (hq : ∀ R j, j ∈ leftEnds₂ ((true, i) :: a) R.val →
  (q R j).1 ≤ R.val.length ∧ OnStrand₂ ((true, i) :: a) R.val j (q R j))
variable (hr : ∀ S j, j ∈ leftEnds₂ a S.val → OnStrand₂ a S.val j (r S j))
variable (τ : ∀ R : {R // R ∈ M}, (MatchingStrand ((true, i) :: a) R.val → ℕ) → List (DTMove I))
variable (υ : ∀ S : {S // S ∈ N}, (MatchingStrand a S.val → ℕ) → List (DTMove I))
variable (hτ : ∀ R c, Decorates₂ ((true, i) :: a) R.val (q R) (strandCounts c) (τ R c))
variable (hυ : ∀ S c, Decorates₂ a S.val (r S) (strandCounts c) (υ S c))


include hM hN hq hr hτ hυ

/-- Coefficientwise BE2 Theorem 10.3 Claim 2 for arbitrary endpoints.
Independent points and all-count serializers precede all signs and
degrees; the labelled equivalence precedes the datum and weight. Neither the
algebraic nor the graphical transport is assumed. The two sides compare every
integer Laurent coefficient of the existing form with finite parity-weighted
strand-label sums, for unrestricted colours without bar consistency. This does
not assert all of Theorem 10.3 or remove the coefficient conventions. -/
theorem rightCup_labelled_form_coeff_iff
    (hMrep : ∀ R, IsMatching₂ ((true, i) :: a) b R → StrictReduced₂ ((true, i) :: a) R →
      ∃ S ∈ M, Iso (pairing₂ ((true, i) :: a) S) (pairing₂ ((true, i) :: a) R))
    (hNrep : ∀ R, IsMatching₂ a ((false, i) :: b) R → StrictReduced₂ a R →
      ∃ S ∈ N, Iso (pairing₂ a S) (pairing₂ a R))
    (hMuniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ ((true, i) :: a) R) (pairing₂ ((true, i) :: a) S) →
      R = S)
    (hNuniq : ∀ R ∈ N, ∀ S ∈ N, Iso (pairing₂ a R) (pairing₂ a S) → R = S) :
    ∃ F : (Σ R : {R // R ∈ M}, MatchingStrand ((true, i) :: a) R.val → ℕ) ≃
        (Σ S : {S // S ∈ N}, MatchingStrand a S.val → ℕ),
      ∀ (D : RootDatum I X) (μ : X),
      let d := fun t : (Σ R : {R // R ∈ M}, MatchingStrand ((true, i) :: a) R.val → ℕ) =>
        tableDegree D.toSKM D.skmSymmetrizer μ (dLay ((true, i) :: a) (τ t.1 t.2))
      let e := fun u : (Σ S : {S // S ∈ N}, MatchingStrand a S.val → ℕ) =>
        tableDegree D.toSKM D.skmSymmetrizer μ (dLay a (υ u.1 u.2))
      let p := fun t : (Σ R : {R // R ∈ M}, MatchingStrand ((true, i) :: a) R.val → ℕ) =>
        xpar D.toSKM μ (dLay ((true, i) :: a) (τ t.1 t.2))
      let p' := fun u : (Σ S : {S // S ∈ N}, MatchingStrand a S.val → ℕ) =>
        xpar D.toSKM μ (dLay a (υ u.1 u.2))
      let δ := (D.d i : ℤ) * (1 + D.h i (wt D.toSKM μ a))
      ∃ (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
        (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
        (∀ t, e (F t) = d t + δ ∧ p' (F t) = p t) ∧
        (∀ z, Nonempty ({t // d t = z - δ} ≃ {u // e u = z})) ∧
        ∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
        ((∀ z : ℤ,
          (signLaurent σ hσ (sesquilinearForm D
            (algebraWord D μ ((true, i) :: a)) (algebraWord D μ b))).coeff z =
              ∑ t ∈ (hf z).toFinset, σ ^ (p t).val) ↔
         (∀ z : ℤ,
          (signLaurent σ hσ (sesquilinearForm D
            (algebraWord D μ a) (algebraWord D μ ((false, i) :: b)))).coeff z =
              ∑ u ∈ (hg z).toFinset, σ ^ (p' u).val)) := by
  obtain ⟨F, hF⟩ := rightCup_labelled_family_coefficients (X := X)
    hM hN q r hq hr τ υ hτ hυ hMrep hNrep hMuniq hNuniq
  refine ⟨F, ?_⟩
  intro D μ
  dsimp only
  obtain ⟨hf, hg, hgrading, hfibers, hsums⟩ := hF D.toSKM D.skmSymmetrizer μ
  refine ⟨hf, hg, hgrading, hfibers, ?_⟩
  intro σ hσ
  by_cases hwt : wt D.toSKM μ b = wt D.toSKM μ a + D.α i
  · have hadjoint := sesquilinearForm_mixed_up_leftCons_bent_coeff D
    constructor
    · intro h z
      exact (hadjoint σ hσ i μ a b hwt z).trans
        ((h _).trans (hsums σ z).symm)
    · intro h z
      have ha := hadjoint σ hσ i μ a b hwt
        (z + (D.d i : ℤ) * (1 + D.h i (wt D.toSKM μ a)))
      have hs := hsums σ (z + (D.d i : ℤ) * (1 + D.h i (wt D.toSKM μ a)))
      simpa only [RootDatum.skmSymmetrizer_d, RootDatum.toSKM_h, add_sub_cancel_right]
        using ha.symm.trans ((h _).trans hs)
  · have hsource : wt D.toSKM μ ((true, i) :: a) ≠ wt D.toSKM μ b := by
      simpa only [wt_cons, sh, RootDatum.toSKM_α, ite_true, add_comm] using Ne.symm hwt
    have htarget : wt D.toSKM μ a ≠ wt D.toSKM μ ((false, i) :: b) := by
      intro he
      apply hwt
      simp only [wt_cons, sh, RootDatum.toSKM_α, Bool.false_eq_true, ite_false] at he
      rw [he]
      abel
    obtain ⟨hform, hform'⟩ := sesquilinearForm_mixed_up_leftCons_mismatch D μ i a b hwt
    have hsum := matching_labelled_finite_sum_eq_zero_of_weight_ne (K := ℚ) D.toSKM μ M
      (fun R hR => (hM R hR).1) hsource
    have hsum' := matching_labelled_finite_sum_eq_zero_of_weight_ne (K := ℚ) D.toSKM μ N
      (fun S hS => (hN S hS).1) htarget
    constructor
    · intro _ z
      rw [hform', hsum']
      simp
    · intro _ z
      rw [hform, hsum]
      simp

end OddMath.SKM
