import OddMath.SKM.CupAttachmentGrading
import OddMath.SKM.PositivePointGradingExamples

/-! A nonempty crossing/dot consumer, with both bottom and top dot placements.
The ordinary input realization is supplied by positive_point_decorated_degree_parity
through the frozen PositivePointGradingExamples.crossing_dot_points theorem. -/

namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove

/-- The literal cup attachment of a positive two-strand crossing with one dot.
Both point placements and repeated colours are allowed. -/
theorem cup_attached_crossing_dot_points {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (i j : I) :
    ∀ ds ∈ [[.dt 0, .tm (.mv (.cross 0))], [.tm (.mv (.cross 0)), .dt 1]],
    ∃ (L : List (LayerData I))
      (hL : SChain [(true, i), (true, j)] L [(true, j), (true, i)])
      (hB : SChain [(true, j)] (cupAttachLayers i [(true, j)] L)
        [(false, i), (true, j), (true, i)]),
      L.map ofL = dLay [(true, i), (true, j)] ds ∧
      (cupAttachLayers i [(true, j)] L).map ofL = dLay [(true, j)] (cupAttachMoves i ds) ∧
      Diagram.degree (gdeg D sy) (mkD D μ L hL) = sy.d i * D.d i j + 2 * sy.d i ∧
      Diagram.degree (gdeg D sy) (mkD D μ (cupAttachLayers i [(true, j)] L) hB) =
        sy.d i * D.d i j + 2 * sy.d i + sy.d i * (1 + D.h i (wt D μ [(true, j)])) ∧
      xpar D μ (dLay [(true, j)] (cupAttachMoves i ds)) =
        D.parity i * D.parity j + D.parity i := by
  intro ds hds
  obtain ⟨L, hL, he, hd, hp⟩ := PositivePointGradingExamples.crossing_dot_points D sy μ i j ds hds
  have hR : IsMatching₂ [(true, i), (true, j)] [(true, j), (true, i)]
      [.mv (.cross 0)] := by
    constructor
    · change 3 < 4 ∧ True
      decide
    · rfl
  have ht : tmoves ds = [.mv (.cross 0)] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hds
    rcases hds with rfl | rfl <;> rfl
  obtain ⟨hB, hbe, hbd, hbp⟩ := cup_attach_up_degree_parity D sy μ hR ht L hL he
  exact ⟨L, hL, hB, he, hbe, hd, by rw [hbd, hd], hbp.trans hp⟩

end OddMath.SKM
