import OddMath.SKM.PositiveMatchingGrading

/-! Boundary and colour checks for the positive-matching degree and parity formula. -/

namespace OddMath.SKM.PositiveMatchingGradingExamples
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators

-- The endpoint permutation is obtained from the existing classification, not assumed.
example {I X : Type*} [AddCommGroup X] (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {n : ℕ} (a b : Fin n → I) {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R)
    (hred : StrictReduced₂ (List.ofFn fun r => (true, a r)) R) :
    ∃ e : Equiv.Perm (Fin n), (∀ r, a r = b (e r)) ∧
      ∃ (L : List (LayerData I))
        (hL : SChain (List.ofFn fun r => (true, a r)) L (List.ofFn fun r => (true, b r))),
        L.map ofL = tLay (List.ofFn fun r => (true, a r)) R ∧
        Diagram.degree (gdeg D sy) (mkD D μ L hL) =
          ∑ r, ∑ s with r < s ∧ e s < e r, sy.d (a r) * D.d (a r) (a s) ∧
        xpar D μ (tLay (List.ofFn fun r => (true, a r)) R) =
          ∑ r, ∑ s with r < s ∧ e s < e r, D.parity (a r) * D.parity (a s) := by
  obtain ⟨hv, hl, hs⟩ := hR.pairing_properties
  obtain ⟨e, ⟨hc, he⟩, _⟩ := positive_pairing_equiv a b hv hl hs
  exact ⟨e, hc, positive_matching_degree_parity D sy μ a b hR hred e he⟩

-- The zero-strand case allows an empty colour type.
example {X : Type*} [AddCommGroup X] (D : Datum Empty X) (sy : Symmetrizer D) (μ : X) :
    ∃ (L : List (LayerData Empty)) (hL : SChain [] L []),
      L.map ofL = tLay [] [] ∧ Diagram.degree (gdeg D sy) (mkD D μ L hL) = 0 ∧
      xpar D μ (tLay [] []) = 0 := by
  let a : Fin 0 → Empty := Fin.elim0
  have hm : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, a r)) [] := ⟨trivial, rfl⟩
  have hr : StrictReduced₂ (List.ofFn fun r => (true, a r)) [] :=
    ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩
  simpa using positive_matching_degree_parity D sy μ a a hm hr (Equiv.refl _)
    (fun r => Fin.elim0 r)

private def twoColours {I : Type*} (i j : I) : Fin 2 → I := ![i, j]
private def swapMoves {I : Type*} : List (TMove (Letter I)) := [.mv (.cross 0)]

/-- One crossing keeps its two colour weights, including when the colours coincide. -/
theorem two_colour_crossing_degree_parity {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (i j : I) :
    ∃ (L : List (LayerData I)) (hL : SChain [(true, i), (true, j)] L [(true, j), (true, i)]),
      L.map ofL = tLay [(true, i), (true, j)] swapMoves ∧
      Diagram.degree (gdeg D sy) (mkD D μ L hL) = sy.d i * D.d i j ∧
      xpar D μ (tLay [(true, i), (true, j)] swapMoves) = D.parity i * D.parity j := by
  have hm : IsMatching₂ (List.ofFn fun r => (true, twoColours i j r))
      (List.ofFn fun r => (true, twoColours j i r)) swapMoves := by
    constructor
    · change 3 < 4 ∧ True
      decide
    · rfl
  have hr : StrictReduced₂ (List.ofFn fun r => (true, twoColours i j r)) swapMoves := by
    refine ⟨⟨List.nodup_singleton _, ?_⟩, List.nodup_nil⟩
    intro z hz
    change z ∈ [_] at hz
    obtain rfl := List.mem_singleton.mp hz
    change ¬ (s(2, 0) : Sym2 ℕ).IsDiag
    decide
  have he : ∀ r : Fin 2, Same
      (pairing₂ (List.ofFn fun r => (true, twoColours i j r)) swapMoves)
      (2 - 1 - r.val) (2 + ((Equiv.swap 0 1) r).val) := by
    intro r
    fin_cases r
    · change 1 ≠ 3 ∧ (some 2 : Option ℕ) ≠ none ∧ (some 2 : Option ℕ) = some 2
      decide
    · change 0 ≠ 2 ∧ (some 0 : Option ℕ) ≠ none ∧ (some 0 : Option ℕ) = some 0
      decide
  simpa [twoColours, Finset.sum_filter, Fin.sum_univ_two] using
    positive_matching_degree_parity D sy μ (twoColours i j) (twoColours j i) hm hr
      (Equiv.swap 0 1) he

-- In particular a crossing of two equal odd colours has odd parity.
example {I X : Type*} [AddCommGroup X] (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    (i : I) (hi : D.parity i = 1) :
    ∃ (L : List (LayerData I)) (hL : SChain [(true, i), (true, i)] L [(true, i), (true, i)]),
      L.map ofL = tLay [(true, i), (true, i)] swapMoves ∧
      Diagram.degree (gdeg D sy) (mkD D μ L hL) = sy.d i * D.d i i ∧
      xpar D μ (tLay [(true, i), (true, i)] swapMoves) = 1 := by
  simpa only [hi, mul_one] using two_colour_crossing_degree_parity D sy μ i i

end OddMath.SKM.PositiveMatchingGradingExamples
