import OddMath.SKM.PositiveMatchingGrading
import OddMath.SKM.PositiveMatchingDots

/-!
# Grading positive top-decorated matchings

Supporting the degree/parity calculation in [BE2, arXiv:1701.04133v2,
Theorem 10.3, proof of Claim 1], with distinguished points as in §8.
The ordinary diagram realizing the top-decorated matching has the existing crossing
inversion contribution plus the top-indexed dot contribution. No finite colour type,
representative enumeration, or default colour is required. This does not prove the
coefficientwise graphical sum, its comparison with the algebraic form, or independence
of representative and distinguished-point choices.
-/

noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators

private theorem sChain_topDotLayers {I : Type*} {a : List (Letter I)}
    {R : List (TMove (Letter I))} {d : ℕ} (b : Fin d → I)
    (p : MatchingStrand a R → Fin d) (c : MatchingStrand a R → ℕ) :
    SChain (List.ofFn fun t => (true, b t)) (topDotLayers b p c)
      (List.ofFn fun t => (true, b t)) := by
  have hd (j : MatchingStrand a R) :
      SChain (List.ofFn fun t => (true, b t))
        (dotsL ((List.ofFn fun t => (true, b t)).take (p j).val) (b (p j))
          ((List.ofFn fun t => (true, b t)).drop ((p j).val + 1)) (c j))
        (List.ofFn fun t => (true, b t)) := by
    have he : (List.ofFn fun t => (true, b t)).take (p j).val ++ [up (b (p j))] ++
        (List.ofFn fun t => (true, b t)).drop ((p j).val + 1) =
        (List.ofFn fun t => (true, b t)) := by
      have hp : (p j).val < (List.ofFn fun t => (true, b t)).length := by simp
      have hs := List.take_append_drop (p j).val (List.ofFn fun t => (true, b t))
      rw [List.drop_eq_getElem_cons hp] at hs
      simpa [List.append_assoc] using hs
    simpa only [he] using sChain_dotsL
      ((List.ofFn fun t => (true, b t)).take (p j).val) (b (p j))
      ((List.ofFn fun t => (true, b t)).drop ((p j).val + 1)) (c j)
  unfold topDotLayers
  induction (leftEnds₂ a R).attach with
  | nil => rfl
  | cons j js ih => exact SChain.append (hd j) ih

private theorem sum_strands_equiv {I β : Type*} [AddCommMonoid β]
    {a : List (Letter I)} {R : List (TMove (Letter I))} {n : ℕ}
    (p : MatchingStrand a R ≃ Fin n) (f : Fin n → β) :
    ((leftEnds₂ a R).attach.map fun j => f (p j)).sum = ∑ t, f t := by
  classical
  have hu : (leftEnds₂ a R).attach.toFinset = Finset.univ := by
    ext j
    simp
  rw [← List.sum_toFinset _ ((nodup_leftEnds₂ a R).attach), hu]
  exact Equiv.sum_comp p f

/-- The existing diagram degree and extended-layer parity of positive strictly reduced
matchings decorated at their top endpoints. Crossing colours are indexed at the source;
dot counts are indexed at the target. The strand equivalence certifies valid distinguished
points, rather than merely relabelling strands. -/
theorem positive_decorated_degree_parity {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {n : ℕ} (a b : Fin n → I) {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R)
    (hred : StrictReduced₂ (List.ofFn fun r => (true, a r)) R)
    (e : Equiv.Perm (Fin n))
    (he : ∀ r, Same (pairing₂ (List.ofFn fun r => (true, a r)) R)
      (n - 1 - r.val) (n + (e r).val)) :
    ∃ p : MatchingStrand (List.ofFn fun r => (true, a r)) R ≃ Fin n,
      (∀ j : MatchingStrand (List.ofFn fun r => (true, a r)) R,
        OnStrand₂ (List.ofFn fun r => (true, a r)) R j.val (R.length, (p j).val)) ∧
      ∀ c : Fin n → ℕ,
        ∃ (L : List (LayerData I))
          (hL : SChain (List.ofFn fun r => (true, a r)) L
            (List.ofFn fun r => (true, b r))),
          L.map ofL = dLay (List.ofFn fun r => (true, a r))
            (topDotMoves (List.ofFn fun r => (true, a r)) R
              (fun j => (p j).val) (fun j => c (p j))) ∧
          Diagram.degree (gdeg D sy) (mkD D μ L hL) =
            (∑ r, ∑ s with r < s ∧ e s < e r,
              sy.d (a r) * D.d (a r) (a s)) +
            ∑ t, (c t : ℤ) * (2 * sy.d (b t)) ∧
          xpar D μ (dLay (List.ofFn fun r => (true, a r))
            (topDotMoves (List.ofFn fun r => (true, a r)) R
              (fun j => (p j).val) (fun j => c (p j)))) =
            (∑ r, ∑ s with r < s ∧ e s < e r,
              D.parity (a r) * D.parity (a s)) +
            ∑ t, (c t : ZMod 2) * D.parity (b t) := by
  classical
  obtain ⟨q, hq, hpoints⟩ := positive_top_points a b hR
  let p := Equiv.ofBijective q hq
  refine ⟨p, hpoints, ?_⟩
  intro c
  obtain ⟨L, hL, hmap, hdeg, hpar⟩ :=
    positive_matching_degree_parity D sy μ a b hR hred e he
  obtain ⟨hm, hd⟩ := topDotMoves_degree D sy μ b hR p (fun j => c (p j)) L hmap
  refine ⟨L ++ topDotLayers b p (fun j => c (p j)),
    SChain.append hL (sChain_topDotLayers b p (fun j => c (p j))), hm, ?_, ?_⟩
  · rw [degree_gdeg_mkD] at hdeg ⊢
    change gsum D sy μ _ = _
    rw [hd, sum_strands_equiv p (fun t => (c t : ℤ) * (2 * sy.d (b t)))]
    exact congrArg (· + _) hdeg
  · rw [topDotMoves_parity D μ b hR, hpar,
      sum_strands_equiv p (fun t => (c t : ZMod 2) * D.parity (b t))]

end OddMath.SKM
