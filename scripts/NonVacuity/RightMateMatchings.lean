import OddMath.SKM.RightMateMatchings

/-! Source-prefix partial mates of a repeated-color crossing: literal
matching, weak reducedness, and decorated ordinary-layer realization. -/

namespace NonVacuity.RightMateMatchings
open StringDiagrams StringDiagrams.Chord OddMath.SKM DTMove

private abbrev W : List (Letter Unit) := [up (), up ()]
private abbrev R : List (TMove (Letter Unit)) := [.mv (.cross 0)]

private theorem matching : IsMatching₂ W W R := by
  constructor
  · change 3 < 4 ∧ True
    decide
  · rfl

private theorem reduced : Reduced₂ W R := by
  change [s(2, 0)].Nodup ∧ ∀ z ∈ [s(2, 0)], ¬ z.IsDiag
  simp

theorem bent_crossing_matching :
    IsMatching₂ [] (dns [(), ()] ++ W) (cupPrefixMatching [(), ()] R) ∧
    Reduced₂ [] (cupPrefixMatching [(), ()] R) ∧
    ncr₂ (cupPrefixMatching [(), ()] R) = 1 :=
  ⟨(cupPrefix_matching_iso [(), ()] matching).1,
    reduced₂_cupPrefix [(), ()] matching reduced,
    (ncr₂_cupPrefix [(), ()] R).trans rfl⟩

theorem bent_crossing_layers :
    (cupPrefixLayers [(), ()] [] (crossL [] () () [])).map ofL =
      dLay [] (cupPrefixMoves [(), ()] [.tm (.mv (.cross 0))]) :=
  dLay_cupPrefix [(), ()] matching rfl rfl

example : MatchingStrand W R ≃ MatchingStrand [] (cupPrefixMatching [(), ()] R) :=
  cupPrefixStrandEquiv [(), ()] matching

example : SChain [] (cupPrefixLayers [(), ()] [] (crossL [] () () []))
    (dns [(), ()] ++ W) :=
  sChain_cupPrefixLayers [(), ()] (show SChain W (crossL [] () () []) W from ⟨rfl, rfl⟩)

private def q (j : ℕ) : ℕ × ℕ := (0, 1 - j)
private def n (j : ℕ) : ℕ := if j = 1 then 1 else 0
private abbrev ds : List (DTMove Unit) := [.dt 0, .tm (.mv (.cross 0))]

private theorem decorated :
    Decorates₂ W R q (strandCounts fun j : MatchingStrand W R => n j) ds := by
  apply (decorates₂_strandCounts_iff q n ds).2
  constructor
  · rfl
  · have hh (x : ℕ) : IsLeftEnd (pairing₂ W R) x ↔ x < 2 :=
      mem_leftEnds₂.symm.trans (positive_mem_leftEnds₂
        (fun _ : Fin 2 => ()) (fun _ : Fin 2 => ()) matching x)
    have hl : leftEnds₂ W R = [0, 1] := by
      unfold leftEnds₂
      simp only [show (pairing₂ W R).length = 4 from rfl, hh]
      decide
    simp [hl, dotPts, n, q]

theorem bent_dotted_crossing :
    Decorates₂ [] (cupPrefixMatching [(), ()] R) (cupPrefixPoint [(), ()] ∘ q)
      (strandCounts ((fun j : MatchingStrand W R => n j) ∘
        (cupPrefixStrandEquiv [(), ()] matching).symm)) (cupPrefixMoves [(), ()] ds) :=
  decorates₂_cupPrefix [(), ()] matching q (fun j => n j) decorated

theorem transported_point :
    (cupPrefixPoint [(), ()] (0, 0)).1 ≤ (cupPrefixMatching [(), ()] R).length ∧
      OnStrand₂ [] (cupPrefixMatching [(), ()] R) 1 (cupPrefixPoint [(), ()] (0, 0)) :=
  onStrand₂_cupPrefix [(), ()] matching (by decide)
    (by change 0 < 2 ∧ 2 = 2; decide)

#print axioms cupPrefix_matching_iso
#print axioms reduced₂_cupPrefix
#print axioms dLay_cupPrefix
#print axioms decorates₂_cupPrefix
#print axioms onStrand₂_cupPrefix
#print axioms cl_rightClosure_cupPrefix
end NonVacuity.RightMateMatchings
