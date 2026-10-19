import OddMath.SKM.PositiveDecoratedGrading

/-! Empty boundaries and repeated odd colours with nonuniform top-dot counts. -/

namespace OddMath.SKM.PositiveDecoratedGradingExamples
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators

-- Empty colour types require neither a default colour nor a nonempty strand set.
example {X : Type*} [AddCommGroup X] (D : Datum Empty X) (sy : Symmetrizer D) (μ : X) :
    ∃ (L : List (LayerData Empty)) (hL : SChain [] L []),
      L.map ofL = [] ∧ Diagram.degree (gdeg D sy) (mkD D μ L hL) = 0 ∧
      xpar D μ (L.map ofL) = 0 := by
  let a : Fin 0 → Empty := Fin.elim0
  have hm : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, a r)) [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ (List.ofFn fun r => (true, a r)) [] :=
    ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
  obtain ⟨p, _, h⟩ := positive_decorated_degree_parity D sy μ a a hm hr
    (Equiv.refl _) (fun r => Fin.elim0 r)
  obtain ⟨L, hL, hm, hd, hp⟩ := h (fun _ => 0)
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · have hz : topDotMoves (List.ofFn fun r => (true, a r)) []
        (fun j => (p j).val) (fun _ => 0) = [] := rfl
    rw [hz] at hm
    exact hm
  · simpa using hd
  · rw [hm]
    simpa using hp

-- One odd crossing and three odd dots have even total parity.
example {I X : Type*} [AddCommGroup X] (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    (i : I) (hi : D.parity i = 1) :
    ∃ p : MatchingStrand [(true, i), (true, i)] [.mv (.cross 0)] ≃ Fin 2,
      (∀ j : MatchingStrand [(true, i), (true, i)] [.mv (.cross 0)],
        OnStrand₂ [(true, i), (true, i)] [.mv (.cross 0)] j.val (1, (p j).val)) ∧
      ∃ (L : List (LayerData I))
        (hL : SChain [(true, i), (true, i)] L [(true, i), (true, i)]),
        L.map ofL = dLay [(true, i), (true, i)]
          (topDotMoves [(true, i), (true, i)] [.mv (.cross 0)]
            (fun j => (p j).val) (fun j => ![1, 2] (p j))) ∧
        Diagram.degree (gdeg D sy) (mkD D μ L hL) =
          sy.d i * D.d i i + 6 * sy.d i ∧
        xpar D μ (L.map ofL) = 0 := by
  let a : Fin 2 → I := fun _ => i
  let R : List (TMove (Letter I)) := [.mv (.cross 0)]
  have hm : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, a r)) R := by
    constructor
    · change 3 < 4 ∧ True
      decide
    · rfl
  have hr : StrictReduced₂ (List.ofFn fun r => (true, a r)) R := by
    refine ⟨⟨List.nodup_singleton _, ?_⟩, List.nodup_nil⟩
    intro z hz
    change z ∈ [_] at hz
    obtain rfl := List.mem_singleton.mp hz
    change ¬ (s(2, 0) : Sym2 ℕ).IsDiag
    decide
  have he : ∀ r : Fin 2, Same (pairing₂ (List.ofFn fun r => (true, a r)) R)
      (2 - 1 - r.val) (2 + ((Equiv.swap 0 1) r).val) := by
    intro r
    fin_cases r
    · change 1 ≠ 3 ∧ (some 2 : Option ℕ) ≠ none ∧ (some 2 : Option ℕ) = some 2
      decide
    · change 0 ≠ 2 ∧ (some 0 : Option ℕ) ≠ none ∧ (some 0 : Option ℕ) = some 0
      decide
  obtain ⟨p, hpoints, h⟩ := positive_decorated_degree_parity D sy μ a a hm hr
    (Equiv.swap 0 1) he
  obtain ⟨L, hL, hm, hd, hp⟩ := h ![1, 2]
  refine ⟨p, hpoints, L, hL, hm, ?_, ?_⟩
  · simp only [Finset.sum_filter, Fin.sum_univ_two] at hd
    simp [a] at hd
    rw [hd]
    ring
  · rw [hm]
    simp only [Finset.sum_filter, Fin.sum_univ_two] at hp
    have hz : (1 + (1 + 2) : ZMod 2) = 0 := by decide
    simpa [a, hi, hz] using hp

end OddMath.SKM.PositiveDecoratedGradingExamples
