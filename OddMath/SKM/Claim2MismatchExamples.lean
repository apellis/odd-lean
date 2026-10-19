import OddMath.SKM.Claim2Coefficients
import OddMath.SKM.PositiveFormCoefficientsExamples

/-! # Coefficientwise BE2 Theorem 10.3 Claim 2 examples -/

noncomputable section
namespace OddMath.SKM.Claim2MismatchExamples
open StringDiagrams StringDiagrams.Chord
open CoveringQuantum CoveringQuantum.UDot.GenericTensor
open CoveringQuantum.Coefficients CoveringQuantum.UDot.GenericVerma.MixedGram
open PositiveDecoratedFamilyCoefficientsExamples PositiveFormCoefficientsExamples
open scoped BigOperators

private def a : List (Letter Unit) := [(true, ()), (false, ())]
private def A : List (Letter Unit) := (true, ()) :: a
private def B : List (Letter Unit) := (false, ()) :: a

private theorem mismatch : wt oddDatum.toSKM 0 a ≠ wt oddDatum.toSKM 0 a + oddDatum.α () := by
  norm_num [a, wt, sh, RootDatum.toSKM_α, oddDatum, RootDatum.α]
private theorem source_mismatch : wt oddDatum.toSKM 0 A ≠ wt oddDatum.toSKM 0 a := by
  norm_num [A, a, wt, sh, RootDatum.toSKM_α, oddDatum, RootDatum.α]
private theorem target_mismatch : wt oddDatum.toSKM 0 a ≠ wt oddDatum.toSKM 0 B := by
  norm_num [B, a, wt, sh, RootDatum.toSKM_α, oddDatum, RootDatum.α]
private theorem source_impossible (R : List (TMove (Letter Unit))) : ¬ IsMatching₂ A a R :=
  not_isMatching₂_of_weight_ne oddDatum.toSKM 0 source_mismatch R
private theorem target_impossible (R : List (TMove (Letter Unit))) : ¬ IsMatching₂ a B R :=
  not_isMatching₂_of_weight_ne oddDatum.toSKM 0 target_mismatch R

/-- Empty representative families are complete here because endpoint conservation
excludes every matching, not because coverage was assumed. -/
private def M : Set (List (TMove (Letter Unit))) := ∅
private def N : Set (List (TMove (Letter Unit))) := ∅
private theorem hM : ∀ R ∈ M, IsMatching₂ A a R ∧ StrictReduced₂ A R := by simp [M]
private theorem hN : ∀ R ∈ N, IsMatching₂ a B R ∧ StrictReduced₂ a R := by simp [N]
private theorem hMrep : ∀ R, IsMatching₂ A a R → StrictReduced₂ A R →
    ∃ S ∈ M, Iso (pairing₂ A S) (pairing₂ A R) := by
  intro R h _
  exact (source_impossible R h).elim
private theorem hNrep : ∀ R, IsMatching₂ a B R → StrictReduced₂ a R →
    ∃ S ∈ N, Iso (pairing₂ a S) (pairing₂ a R) := by
  intro R h _
  exact (target_impossible R h).elim
private theorem hMuniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ A R) (pairing₂ A S) → R = S := by
  simp [M]
private theorem hNuniq : ∀ R ∈ N, ∀ S ∈ N, Iso (pairing₂ a R) (pairing₂ a S) → R = S := by
  simp [N]
private def q (_ : {R // R ∈ M}) (_ : ℕ) : ℕ × ℕ := (0, 0)
private def r (_ : {R // R ∈ N}) (_ : ℕ) : ℕ × ℕ := (0, 1)
private theorem hq : ∀ R j, j ∈ leftEnds₂ A R.val →
    (q R j).1 ≤ R.val.length ∧ OnStrand₂ A R.val j (q R j) := by
  intro R
  exact (Set.notMem_empty R.val R.property).elim
private theorem hr : ∀ R j, j ∈ leftEnds₂ a R.val → OnStrand₂ a R.val j (r R j) := by
  intro R
  exact (Set.notMem_empty R.val R.property).elim
private def sourceSerializer (R : {R // R ∈ M}) (_ : MatchingStrand A R.val → ℕ) : List (DTMove Unit) :=
  (Set.notMem_empty R.val R.property).elim
private def targetSerializer (R : {R // R ∈ N}) (_ : MatchingStrand a R.val → ℕ) : List (DTMove Unit) :=
  (Set.notMem_empty R.val R.property).elim
private theorem hτ (R : {R // R ∈ M}) (c : MatchingStrand A R.val → ℕ) :
    Decorates₂ A R.val (q R) (strandCounts c) (sourceSerializer R c) :=
  (Set.notMem_empty R.val R.property).elim
private theorem hυ (R : {R // R ∈ N}) (c : MatchingStrand a R.val → ℕ) :
    Decorates₂ a R.val (r R) (strandCounts c) (targetSerializer R c) :=
  (Set.notMem_empty R.val R.property).elim
private abbrev T := Σ R : {R // R ∈ M}, MatchingStrand A R.val → ℕ
private abbrev U := Σ R : {R // R ∈ N}, MatchingStrand a R.val → ℕ
private def d (t : T) : ℤ := tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
  (dLay A (sourceSerializer t.1 t.2))
private def e (u : U) : ℤ := tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0
  (dLay a (targetSerializer u.1 u.2))
private def p (t : T) : ZMod 2 := xpar oddDatum.toSKM 0 (dLay A (sourceSerializer t.1 t.2))
private def p' (u : U) : ZMod 2 := xpar oddDatum.toSKM 0 (dLay a (targetSerializer u.1 u.2))

/-- Both different physical forms vanish by actual block orthogonality. -/
theorem forms_zero :
    sesquilinearForm oddDatum odd_barConsistent (algebraWord oddDatum 0 A)
      (algebraWord oddDatum 0 a) = 0 ∧
    sesquilinearForm oddDatum odd_barConsistent (algebraWord oddDatum 0 a)
      (algebraWord oddDatum 0 B) = 0 :=
  sesquilinearForm_mixed_up_leftCons_mismatch oddDatum odd_barConsistent 0 () a a mismatch

/-- Invoke the endpoint-unrestricted headline on complete mismatch families.
The actual two form assertions occur in the iff, and the same finite witnesses
have both coefficients and both graphical sums zero for both signs and all degrees. -/
theorem mismatch_form_coeff_iff :
    ∃ (hf : ∀ z : ℤ, Set.Finite {t : T | d t = z})
      (hg : ∀ z : ℤ, Set.Finite {u : U | e u = z}),
      (∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
        ((∀ z : ℤ,
          (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
            (algebraWord oddDatum 0 A) (algebraWord oddDatum 0 a))).coeff z =
              ∑ t ∈ (hf z).toFinset, σ ^ (p t).val) ↔
         (∀ z : ℤ,
          (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
            (algebraWord oddDatum 0 a) (algebraWord oddDatum 0 B))).coeff z =
              ∑ u ∈ (hg z).toFinset, σ ^ (p' u).val))) ∧
      ∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
        (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
          (algebraWord oddDatum 0 A) (algebraWord oddDatum 0 a))).coeff z = 0 ∧
        (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
          (algebraWord oddDatum 0 a) (algebraWord oddDatum 0 B))).coeff z = 0 ∧
        (∑ t ∈ (hf z).toFinset, σ ^ (p t).val) = 0 ∧
        (∑ u ∈ (hg z).toFinset, σ ^ (p' u).val) = 0 := by
  obtain ⟨_, hF⟩ := rightCup_labelled_form_coeff_iff (X := ℤ)
    hM hN q r hq hr sourceSerializer targetSerializer hτ hυ hMrep hNrep hMuniq hNuniq
  obtain ⟨hf, hg, _, _, hiff⟩ := hF oddDatum odd_barConsistent 0
  refine ⟨hf, hg, hiff, ?_⟩
  intro σ hσ z
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [forms_zero.1]
    simp
  · rw [forms_zero.2]
    simp
  · exact matching_labelled_finite_sum_eq_zero_of_weight_ne oddDatum.toSKM 0 M
      (fun R hR => (hM R hR).1) source_mismatch (hf z).toFinset _
  · exact matching_labelled_finite_sum_eq_zero_of_weight_ne oddDatum.toSKM 0 N
      (fun R hR => (hN R hR).1) target_mismatch (hg z).toFinset _

end OddMath.SKM.Claim2MismatchExamples
