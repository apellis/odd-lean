import OddMath.SKM.BoundaryFamily
import OddMath.SKM.LeftCupFamilyCoefficients

/-! Finite graphical coefficients in BE2 v2 Theorem 10.3 Claim 4.
Independent points and all-natural serializers precede the grading parameters.
The representative and strand correspondences and fiber finiteness are derived. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators
variable {I X : Type*} [AddCommGroup X]

/-- Decorated normalization, using the endpoint-reindexed strand counts. -/
theorem opposite_boundary_decorated_degree_parity
    (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    (a b : List (Letter I)) (i j : I) (hij : i ≠ j)
    {R S : List (TMove (Letter I))}
    (hR : IsMatching₂ (a ++ (true, i) :: (false, j) :: b) [] R)
    (hrR : Reduced₂ (a ++ (true, i) :: (false, j) :: b) R)
    (hS : IsMatching₂ (a ++ (false, j) :: (true, i) :: b) [] S)
    (hrS : Reduced₂ (a ++ (false, j) :: (true, i) :: b) S)
    (hi : Iso (pairing₂ (a ++ (false, j) :: (true, i) :: b) S)
      (swapAt (pairing₂ (a ++ (true, i) :: (false, j) :: b) R) b.length))
    (q r : ℕ → ℕ × ℕ)
    (hq : ∀ k ∈ leftEnds₂ (a ++ (true, i) :: (false, j) :: b) R,
      OnStrand₂ (a ++ (true, i) :: (false, j) :: b) R k (q k))
    (hr : ∀ k ∈ leftEnds₂ (a ++ (false, j) :: (true, i) :: b) S,
      OnStrand₂ (a ++ (false, j) :: (true, i) :: b) S k (r k))
    (c : MatchingStrand (a ++ (true, i) :: (false, j) :: b) R → ℕ)
    (ds es : List (DTMove I))
    (hd : Decorates₂ (a ++ (true, i) :: (false, j) :: b) R q (strandCounts c) ds)
    (he : Decorates₂ (a ++ (false, j) :: (true, i) :: b) S r
      (strandCounts (c ∘ (matchingStrandEquivOfSwap
        (boundary_swap_strand_data a b (true, i) (false, j) hij hR).1
        (boundary_swap_strand_data a b (true, i) (false, j) hij hR).2 hi).symm)) es) :
    tableDegree D sy μ (dLay (a ++ (false, j) :: (true, i) :: b) es) =
      tableDegree D sy μ (dLay (a ++ (true, i) :: (false, j) :: b) ds) ∧
    xpar D μ (dLay (a ++ (false, j) :: (true, i) :: b) es) =
      xpar D μ (dLay (a ++ (true, i) :: (false, j) :: b) ds) + D.parity i * D.parity j := by
  obtain ⟨hdR, hpR⟩ := mixed_decorated_degree_parity D sy μ hR q hq c ds hd
  obtain ⟨hdS, hpS⟩ := mixed_decorated_degree_parity D sy μ hS r hr _ es he
  obtain ⟨hb, hp⟩ := reduced₂_opposite_boundary_degree_parity D sy μ a b i j hij hR hrR hS hrS hi
  have H := boundary_swap_strand_data a b (true, i) (false, j) hij hR
  rw [matchingStrand_swap_sum H.1 H.2 hi c (fun n k => (n : ℤ) * (2 * sy.d k))] at hdS
  rw [matchingStrand_swap_sum H.1 H.2 hi c (fun n k => (n : ZMod 2) * D.parity k)] at hpS
  constructor
  · rw [hdR, hdS, hb]
  · rw [hpR, hpS, hp]
    ac_rfl

section Family
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

/-- Graphical Claim 4: the finite coefficients differ by the crossing parity.
No equivalence, colour map, finite fiber, grading or enumeration identity is assumed.
The result includes both directions at every square-one rational specialization. -/
theorem opposite_boundary_labelled_family_coefficients
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
      ∀ (D : Datum I X) (sy : Symmetrizer D) (μ : X),
      let d := fun t : (Σ R : {R // R ∈ M}, MatchingStrand (a ++ (true, i) :: (false, j) :: b) R.val → ℕ) =>
        tableDegree D sy μ (dLay (a ++ (true, i) :: (false, j) :: b) (τ t.1 t.2))
      let e := fun u : (Σ S : {S // S ∈ N}, MatchingStrand (a ++ (false, j) :: (true, i) :: b) S.val → ℕ) =>
        tableDegree D sy μ (dLay (a ++ (false, j) :: (true, i) :: b) (υ u.1 u.2))
      let p := fun t : (Σ R : {R // R ∈ M}, MatchingStrand (a ++ (true, i) :: (false, j) :: b) R.val → ℕ) =>
        xpar D μ (dLay (a ++ (true, i) :: (false, j) :: b) (τ t.1 t.2))
      let p' := fun u : (Σ S : {S // S ∈ N}, MatchingStrand (a ++ (false, j) :: (true, i) :: b) S.val → ℕ) =>
        xpar D μ (dLay (a ++ (false, j) :: (true, i) :: b) (υ u.1 u.2))
      let p₀ := D.parity i * D.parity j
      ∃ (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
        (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
        (∀ t, e (F t) = d t ∧ p' (F t) = p t + p₀) ∧
        (∀ z, Nonempty ({t // d t = z} ≃ {u // e u = z})) ∧
        ∀ (σ : ℚ), σ ^ 2 = 1 → ∀ (z : ℤ),
          (∑ u ∈ (hg z).toFinset, σ ^ (p' u).val) =
            σ ^ p₀.val * ∑ t ∈ (hf z).toFinset, σ ^ (p t).val ∧
          (∑ t ∈ (hf z).toFinset, σ ^ (p t).val) =
            σ ^ p₀.val * ∑ u ∈ (hg z).toFinset, σ ^ (p' u).val := by
  obtain ⟨E, hE⟩ := boundary_swap_representatives_equiv a b (true, i) (false, j) M N
    hM hN hMrep hNrep hMuniq hNuniq
  let F := boundarySwapLabelledEquiv hij (fun R hR => (hM R hR).1) E hE
  refine ⟨F, ?_⟩
  intro D sy μ
  dsimp only
  have h (t : Σ R : {R // R ∈ M}, MatchingStrand (a ++ (true, i) :: (false, j) :: b) R.val → ℕ) :
      tableDegree D sy μ (dLay (a ++ (false, j) :: (true, i) :: b) (υ (F t).1 (F t).2)) =
        tableDegree D sy μ (dLay (a ++ (true, i) :: (false, j) :: b) (τ t.1 t.2)) ∧
      xpar D μ (dLay (a ++ (false, j) :: (true, i) :: b) (υ (F t).1 (F t).2)) =
        xpar D μ (dLay (a ++ (true, i) :: (false, j) :: b) (τ t.1 t.2)) + D.parity i * D.parity j :=
    opposite_boundary_decorated_degree_parity D sy μ a b i j hij
    (hM t.1 t.1.property).1 (hM t.1 t.1.property).2.1
    (hN (E t.1) (E t.1).property).1 (hN (E t.1) (E t.1).property).2.1
    (hE t.1) (q t.1) (r (E t.1)) (hq t.1) (hr (E t.1)) t.2 _ _ (hτ _ _) (hυ _ _)
  have hf := mixed_labelled_degree_finite D sy μ _ [] M
    (fun R hR => (hM R hR).1) hMuniq q hq τ hτ
  have hg := mixed_labelled_degree_finite D sy μ _ [] N
    (fun S hS => (hN S hS).1) hNuniq r hr υ hυ
  refine ⟨hf, hg, h, ?_, ?_⟩
  · intro z
    exact ⟨F.subtypeEquiv (fun t => by rw [(h t).1])⟩
  · intro σ hσ z
    obtain ⟨_, heq⟩ := degreeShift_finite_sum F
      (fun t => tableDegree D sy μ (dLay (a ++ (true, i) :: (false, j) :: b) (τ t.1 t.2)))
      (fun u => tableDegree D sy μ (dLay (a ++ (false, j) :: (true, i) :: b) (υ u.1 u.2)))
      (fun t => σ ^ (D.parity i * D.parity j).val * σ ^ (xpar D μ (dLay (a ++ (true, i) :: (false, j) :: b) (τ t.1 t.2))).val)
      (fun u => σ ^ (xpar D μ (dLay (a ++ (false, j) :: (true, i) :: b) (υ u.1 u.2))).val)
      0 (fun t => by simpa using (h t).1) (fun t => by
        rw [(h t).2, parity_pow_add σ hσ, mul_comm]) z (by simpa using hf z)
    simp only [sub_zero] at heq
    have heq' := heq.trans (Finset.mul_sum _ _ _).symm
    refine ⟨heq', ?_⟩
    rw [heq', ← mul_assoc]
    have hs : σ ^ (D.parity i * D.parity j).val * σ ^ (D.parity i * D.parity j).val = 1 := by
      rw [← parity_pow_add σ hσ, ← two_mul, show (2 : ZMod 2) = 0 from rfl,
        zero_mul, ZMod.val_zero, pow_zero]
    rw [hs, one_mul]
end Family
end OddMath.SKM
