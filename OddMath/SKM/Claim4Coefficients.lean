import OddMath.SKM.BoundaryFamilyCoefficients
import OddMath.CoveringQuantum.UDot.ContextualExchange

/-! # Coefficientwise distinct-colour boundary exchange

BE2, arXiv:1701.04133v2, Theorem 10.3 Claim 4 for distinguished points
and natural strand labels. The labelled equivalence precedes the root datum,
bar consistency and weight; both finite fibers precede the sign and degree.
This coefficientwise statement retains finite colours, bar consistency, additive
weights and decidable equalities over purely-even covering coefficients.
It does not assert the whole formal-series identity or all of Theorem 10.3.
-/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open CoveringQuantum CoveringQuantum.UDot.GenericTensor
open CoveringQuantum.Coefficients CoveringQuantum.UDot.GenericVerma.MixedGram
open scoped BigOperators
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable {i j : I} {a b : List (Letter I)}
variable {M N : Set (List (TMove (Letter I)))}
variable (hij : i ≠ j)
variable (hM : ∀ R ∈ M, IsMatching₂ (a ++ (true, i) :: (false, j) :: b) [] R ∧
  StrictReduced₂ (a ++ (true, i) :: (false, j) :: b) R)
variable (hN : ∀ S ∈ N, IsMatching₂ (a ++ (false, j) :: (true, i) :: b) [] S ∧
  StrictReduced₂ (a ++ (false, j) :: (true, i) :: b) S)
variable (q : {R // R ∈ M} → ℕ → ℕ × ℕ) (r : {S // S ∈ N} → ℕ → ℕ × ℕ)
variable (hq : ∀ R k, k ∈ leftEnds₂ (a ++ (true, i) :: (false, j) :: b) R.val →
  OnStrand₂ (a ++ (true, i) :: (false, j) :: b) R.val k (q R k))
variable (hr : ∀ S k, k ∈ leftEnds₂ (a ++ (false, j) :: (true, i) :: b) S.val →
  OnStrand₂ (a ++ (false, j) :: (true, i) :: b) S.val k (r S k))
variable (τ : ∀ R : {R // R ∈ M},
  (MatchingStrand (a ++ (true, i) :: (false, j) :: b) R.val → ℕ) → List (DTMove I))
variable (υ : ∀ S : {S // S ∈ N},
  (MatchingStrand (a ++ (false, j) :: (true, i) :: b) S.val → ℕ) → List (DTMove I))
variable (hτ : ∀ R c, Decorates₂ (a ++ (true, i) :: (false, j) :: b) R.val (q R) (strandCounts c) (τ R c))
variable (hυ : ∀ S c, Decorates₂ (a ++ (false, j) :: (true, i) :: b) S.val (r S) (strandCounts c) (υ S c))

include hij hM hN hq hr hτ hυ

/-- Coefficientwise Claim 4 at every endpoint. Both graphical and algebraic
exchange are proved, not assumed; no grading, enumeration, form equality or
endpoint premise is required. The points and all-count serializers are fixed
before all grading data. Finite colours and bar consistency are the restrictions
of the existing sesquilinear form construction. -/
theorem opposite_boundary_labelled_form_coeff_iff
    (hMrep : ∀ R, IsMatching₂ (a ++ (true, i) :: (false, j) :: b) [] R →
      StrictReduced₂ (a ++ (true, i) :: (false, j) :: b) R →
      ∃ S ∈ M, Iso (pairing₂ (a ++ (true, i) :: (false, j) :: b) S)
        (pairing₂ (a ++ (true, i) :: (false, j) :: b) R))
    (hNrep : ∀ R, IsMatching₂ (a ++ (false, j) :: (true, i) :: b) [] R →
      StrictReduced₂ (a ++ (false, j) :: (true, i) :: b) R →
      ∃ S ∈ N, Iso (pairing₂ (a ++ (false, j) :: (true, i) :: b) S)
        (pairing₂ (a ++ (false, j) :: (true, i) :: b) R))
    (hMuniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ (a ++ (true, i) :: (false, j) :: b) R)
      (pairing₂ (a ++ (true, i) :: (false, j) :: b) S) → R = S)
    (hNuniq : ∀ R ∈ N, ∀ S ∈ N, Iso (pairing₂ (a ++ (false, j) :: (true, i) :: b) R)
      (pairing₂ (a ++ (false, j) :: (true, i) :: b) S) → R = S) :
    ∃ F : (Σ R : {R // R ∈ M}, MatchingStrand (a ++ (true, i) :: (false, j) :: b) R.val → ℕ) ≃
        (Σ S : {S // S ∈ N}, MatchingStrand (a ++ (false, j) :: (true, i) :: b) S.val → ℕ),
      ∀ (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (μ : X),
      let d := fun t : (Σ R : {R // R ∈ M}, MatchingStrand (a ++ (true, i) :: (false, j) :: b) R.val → ℕ) =>
        tableDegree D.toSKM D.skmSymmetrizer μ (dLay (a ++ (true, i) :: (false, j) :: b) (τ t.1 t.2))
      let e := fun u : (Σ S : {S // S ∈ N}, MatchingStrand (a ++ (false, j) :: (true, i) :: b) S.val → ℕ) =>
        tableDegree D.toSKM D.skmSymmetrizer μ (dLay (a ++ (false, j) :: (true, i) :: b) (υ u.1 u.2))
      let p := fun t : (Σ R : {R // R ∈ M}, MatchingStrand (a ++ (true, i) :: (false, j) :: b) R.val → ℕ) =>
        xpar D.toSKM μ (dLay (a ++ (true, i) :: (false, j) :: b) (τ t.1 t.2))
      let p' := fun u : (Σ S : {S // S ∈ N}, MatchingStrand (a ++ (false, j) :: (true, i) :: b) S.val → ℕ) =>
        xpar D.toSKM μ (dLay (a ++ (false, j) :: (true, i) :: b) (υ u.1 u.2))
      let p₀ := D.parity i * D.parity j
      ∃ (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
        (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
        (∀ t, e (F t) = d t ∧ p' (F t) = p t + p₀) ∧
        (∀ z, Nonempty ({t // d t = z} ≃ {u // e u = z})) ∧
        ∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
        ((∀ z : ℤ,
          (signLaurent σ hσ (sesquilinearForm D hD
            (algebraWord D μ (a ++ (true, i) :: (false, j) :: b))
            (algebraWord D μ []))).coeff z =
              ∑ t ∈ (hf z).toFinset, σ ^ (p t).val) ↔
         (∀ z : ℤ,
          (signLaurent σ hσ (sesquilinearForm D hD
            (algebraWord D μ (a ++ (false, j) :: (true, i) :: b))
            (algebraWord D μ []))).coeff z =
              ∑ u ∈ (hg z).toFinset, σ ^ (p' u).val)) := by
  obtain ⟨F, hF⟩ := opposite_boundary_labelled_family_coefficients (X := X)
    hij hM hN q r hq hr τ υ hτ hυ hMrep hNrep hMuniq hNuniq
  refine ⟨F, ?_⟩
  intro D hD μ
  dsimp only
  obtain ⟨hf, hg, hgrading, hfibers, hsums⟩ := hF D.toSKM D.skmSymmetrizer μ
  refine ⟨hf, hg, hgrading, hfibers, ?_⟩
  intro σ hσ
  have ha := sesquilinearForm_context_EF_ne_coeff D hD σ hσ μ a b i j hij
  have hn : σ ≠ 0 := by intro hz; simp [hz] at hσ
  constructor
  · intro h z
    have he := (ha z).symm.trans ((h z).trans (hsums σ hσ z).2)
    exact mul_left_cancel₀ (pow_ne_zero _ hn) he
  · intro h z
    exact (ha z).trans ((congrArg (fun v : ℚ =>
      σ ^ (D.parity i * D.parity j).val * v) (h z)).trans (hsums σ hσ z).2.symm)

end OddMath.SKM
