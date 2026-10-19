import OddMath.SKM.CupFamilyCoefficients
import OddMath.SKM.LeftCupNormalization

/-! # Strand-labelled left-cup coefficient transport

The graphical left-cup step of BE2, arXiv:1701.04133v2, Theorem 10.3,
Claim 3. Physical words read left to right and diagrams bottom to top;
the left-cup region is `wt D μ a`. The generator contributes degree
`dᵢ(1-hᵢν)` and parity `|i,ν|`. The algebraic form comparison is separate.
-/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators
variable {I X : Type*} [AddCommGroup X]

/-- Specialization of parity addition requires a square-one scalar. -/
theorem parity_pow_add (σ : ℚ) (hσ : σ ^ 2 = 1) (p q : ZMod 2) :
    σ ^ (p + q).val = σ ^ p.val * σ ^ q.val := by
  fin_cases p <;> fin_cases q <;> norm_num [pow_two] at hσ ⊢
  have hz : (2 : ZMod 2) = 0 := by decide
  rw [hz]
  simpa only [ZMod.val_zero, show (1 : ZMod 2).val = 1 from rfl, pow_zero, pow_one]
    using hσ.symm

section LeftCup
variable {i : I} {a b : List (Letter I)}
variable {M N : Set (List (TMove (Letter I)))}
variable (hM : ∀ R ∈ M, IsMatching₂ ((false, i) :: a) b R ∧ StrictReduced₂ ((false, i) :: a) R)
variable (hN : ∀ S ∈ N, IsMatching₂ a ((true, i) :: b) S ∧ StrictReduced₂ a S)
variable (q : {R // R ∈ M} → ℕ → ℕ × ℕ)
variable (r : {S // S ∈ N} → ℕ → ℕ × ℕ)
variable (hq : ∀ R j, j ∈ leftEnds₂ ((false, i) :: a) R.val →
  (q R j).1 ≤ R.val.length ∧ OnStrand₂ ((false, i) :: a) R.val j (q R j))
variable (hr : ∀ S j, j ∈ leftEnds₂ a S.val → OnStrand₂ a S.val j (r S j))
variable (τ : ∀ R : {R // R ∈ M}, (MatchingStrand ((false, i) :: a) R.val → ℕ) → List (DTMove I))
variable (υ : ∀ S : {S // S ∈ N}, (MatchingStrand a S.val → ℕ) → List (DTMove I))
variable (hτ : ∀ R c, Decorates₂ ((false, i) :: a) R.val (q R) (strandCounts c) (τ R c))
variable (hυ : ∀ S c, Decorates₂ a S.val (r S) (strandCounts c) (υ S c))

include hM hN hq hr hτ hυ

/-- The lifted representative bijection has the degree and parity dictated by
the literal generator table, for independently fixed valid serializations. -/
theorem leftCup_labelled_degree_parity
    (E : {R // R ∈ M} ≃ {S // S ∈ N})
    (hE : ∀ R, Iso (pairing₂ ((false, i) :: a) R.val) (pairing₂ a (E R).val))
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (t : (Σ R : {R // R ∈ M}, MatchingStrand ((false, i) :: a) R.val → ℕ)) :
    let u := strandLabelledEquiv E hE t
    tableDegree D sy μ (dLay a (υ u.1 u.2)) =
      tableDegree D sy μ (dLay ((false, i) :: a) (τ t.1 t.2)) + sy.d i * (1 - D.h i (wt D μ a)) ∧
    xpar D μ (dLay a (υ u.1 u.2)) = xpar D μ (dLay ((false, i) :: a) (τ t.1 t.2)) + ipar D i (wt D μ a) := by
  rcases t with ⟨R, c⟩
  exact leftCupAttach_normalized_decorated_degree_parity D sy μ
    (hM R R.property).1 (hM R R.property).2.1
    (hN (E R) (E R).property).1 (hN (E R) (E R).property).2.1 (hE R)
    (q R) (r (E R)) (hq R) (hr (E R)) c _ _ (hτ R c) (hυ _ _)

/-- The left-cup graphical coefficients of BE2 Theorem 10.3, Claim 3.
Both fibers are finite by matching, uniqueness and positive dot weights.
The strand-labelled equivalence and independent points/serializers are fixed
before all data, weights, signs and degrees. The parity factor is retained at
both square-one rational specializations. No algebraic form equality is assumed. -/
theorem leftCup_labelled_family_coefficients
    (hMrep : ∀ R, IsMatching₂ ((false, i) :: a) b R → StrictReduced₂ ((false, i) :: a) R →
      ∃ S ∈ M, Iso (pairing₂ ((false, i) :: a) S) (pairing₂ ((false, i) :: a) R))
    (hNrep : ∀ R, IsMatching₂ a ((true, i) :: b) R → StrictReduced₂ a R →
      ∃ S ∈ N, Iso (pairing₂ a S) (pairing₂ a R))
    (hMuniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ ((false, i) :: a) R) (pairing₂ ((false, i) :: a) S) → R = S)
    (hNuniq : ∀ R ∈ N, ∀ S ∈ N, Iso (pairing₂ a R) (pairing₂ a S) → R = S) :
    ∃ F : (Σ R : {R // R ∈ M}, MatchingStrand ((false, i) :: a) R.val → ℕ) ≃
        (Σ S : {S // S ∈ N}, MatchingStrand a S.val → ℕ),
      ∀ (D : Datum I X) (sy : Symmetrizer D) (μ : X),
      let d := fun t : (Σ R : {R // R ∈ M}, MatchingStrand ((false, i) :: a) R.val → ℕ) =>
        tableDegree D sy μ (dLay ((false, i) :: a) (τ t.1 t.2))
      let e := fun u : (Σ S : {S // S ∈ N}, MatchingStrand a S.val → ℕ) =>
        tableDegree D sy μ (dLay a (υ u.1 u.2))
      let p := fun t : (Σ R : {R // R ∈ M}, MatchingStrand ((false, i) :: a) R.val → ℕ) =>
        xpar D μ (dLay ((false, i) :: a) (τ t.1 t.2))
      let p' := fun u : (Σ S : {S // S ∈ N}, MatchingStrand a S.val → ℕ) =>
        xpar D μ (dLay a (υ u.1 u.2))
      let δ := sy.d i * (1 - D.h i (wt D μ a))
      let p₀ := ipar D i (wt D μ a)
      ∃ (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
        (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
        (∀ t, e (F t) = d t + δ ∧ p' (F t) = p t + p₀) ∧
        (∀ z, Nonempty ({t // d t = z - δ} ≃ {u // e u = z})) ∧
        ∀ (σ : ℚ), σ ^ 2 = 1 → ∀ (z : ℤ),
          (∑ u ∈ (hg z).toFinset, σ ^ (p' u).val) =
            σ ^ p₀.val * ∑ t ∈ (hf (z - δ)).toFinset, σ ^ (p t).val := by
  obtain ⟨E, hE⟩ := bending_representatives_equiv (false, i) a b M N
    hM hN hMrep hNrep hMuniq hNuniq
  let hE' := fun R => (hE R).symm
  let F := strandLabelledEquiv E hE'
  refine ⟨F, ?_⟩
  intro D sy μ
  dsimp only
  have h := leftCup_labelled_degree_parity hM hN q r hq hr τ υ hτ hυ E hE' D sy μ
  have hf := mixed_labelled_degree_finite D sy μ ((false, i) :: a) b M
    (fun R hR => (hM R hR).1) hMuniq q (fun R j hj => (hq R j hj).2) τ hτ
  have hg := mixed_labelled_degree_finite D sy μ a ((true, i) :: b) N
    (fun S hS => (hN S hS).1) hNuniq r hr υ hυ
  refine ⟨hf, hg, h, ?_, ?_⟩
  · intro z
    exact ⟨degreeShiftFiberEquiv F _ _ _ (fun t => (h t).1) z⟩
  · intro σ hσ z
    obtain ⟨_, heq⟩ := degreeShift_finite_sum F
      (fun t => tableDegree D sy μ (dLay ((false, i) :: a) (τ t.1 t.2)))
      (fun u => tableDegree D sy μ (dLay a (υ u.1 u.2)))
      (fun t => σ ^ (ipar D i (wt D μ a)).val *
        σ ^ (xpar D μ (dLay ((false, i) :: a) (τ t.1 t.2))).val)
      (fun u => σ ^ (xpar D μ (dLay a (υ u.1 u.2))).val)
      (sy.d i * (1 - D.h i (wt D μ a))) (fun t => (h t).1) (fun t => by
        rw [(h t).2, parity_pow_add σ hσ, mul_comm]) z (hf _)
    exact heq.trans (Finset.mul_sum _ _ _).symm

end LeftCup
end OddMath.SKM
