import OddMath.SKM.WeakMateChoice

/-!
# Layer evaluation of literal inverse mates

Identifies the decorated matching construction with the ordinary adjunction
layers used by the BE2 upward-to-oriented closure calculation.
-/
namespace OddMath.SKM.WeakMate
open StringDiagrams StringDiagrams.Chord DTMove RightCapAttachment
variable {I : Type*}

theorem dualW_ups (r : List I) : dualW (ups r) = dns r := by
  simp [dualW, ups, dns, List.map_map, Function.comp_def, flipL]

theorem suffixLayers_ups (r : List I) (b : List (Letter I)) (L : List (LayerData I)) :
    suffixLayers b (ups r) (L.map ofL) =
      ((L.map (whL [] (dns r))) ++ (capN r).map (whL b [])).map ofL := by
  induction r generalizing b L with
  | nil => simp [suffixLayers, capN]
  | cons i r ih =>
    simp [ups_cons, suffixLayers, ih, dns_cons, capN, List.map_append,
      List.map_map, Function.comp_def, ofL, xwhL, whL, xCapL, flipL, up, dn,
      List.append_assoc]

/-- Actual decorations at actual strand points have valid dot positions. -/
theorem decorates_valid {a : List (Letter I)} {R : List (TMove (Letter I))}
    (q : ℕ → ℕ × ℕ) (hq : ∀ j ∈ leftEnds₂ a R, OnStrand₂ a R j (q j))
    {n : ℕ → ℕ} {ds : List (DTMove I)} (hd : Decorates₂ a R q n ds) : DOk₂ a ds := by
  apply dOk₂_of_dotPts
  intro p hp
  obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp (hd.2.subset hp)
  rw [List.eq_of_mem_replicate hp, hd.1]
  exact (hq j hj).1


/-- Literal cup/cap decorated moves evaluate to exactly the ordinary partial
right mate used by the closure identity. -/
theorem dLay_moves {l r : List I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (ups l ++ a) (b ++ ups r) R)
    (q : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ (ups l ++ a) R,
      (q j).1 ≤ R.length ∧ OnStrand₂ (ups l ++ a) R j (q j))
    (n : MatchingStrand (ups l ++ a) R → ℕ) {ds : List (DTMove I)}
    (hd : Decorates₂ (ups l ++ a) R q (strandCounts n) ds)
    {L : List (LayerData I)} (hL : L.map ofL = dLay (ups l ++ a) ds) :
    dLay (a ++ dns r) (moves l b (ups r) ds) =
      (partialRightMateL l r a b L).map ofL := by
  have hp := decorates₂_cupPrefix l hR q n hd
  have hv : DOk₂ a (cupPrefixMoves l ds) := by
    apply decorates_valid (cupPrefixPoint l ∘ q) _ hp
    intro j hj
    rw [leftEnds₂_cupPrefix l hR] at hj
    exact (onStrand₂_cupPrefix l hR (hq j hj).1 (hq j hj).2).2
  rw [← dualW_ups r]
  unfold moves
  rw [dLay_suffixMoves (prefix_matching hR) hp.1 hv,
    ← dLay_cupPrefix l hR hd.1 hL, suffixLayers_ups, cupPrefixLayers_eq]
  simp [partialRightMateL, List.map_append, List.map_map, Function.comp_def,
    whL, List.append_assoc]

end OddMath.SKM.WeakMate
