import OddMath.SKM.ContextualCrossDecorations

/-! A single strict representative with bounded points and actual serializers.
This packages local adapted constructions before assembling complete families. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove
universe u
variable {I : Type u}

structure PointedMatching (a b : List (Letter I)) where
  moves : List (TMove (Letter I))
  matching : IsMatching₂ a b moves
  strict : StrictReduced₂ a moves
  points : ℕ → ℕ × ℕ
  bounded : ∀ j ∈ leftEnds₂ a moves, (points j).1 ≤ moves.length
  onStrand : ∀ j ∈ leftEnds₂ a moves, OnStrand₂ a moves j (points j)
  serialize : (MatchingStrand a moves → ℕ) → List (DTMove I)
  decorates : ∀ n, Decorates₂ a moves points (strandCounts n) (serialize n)

namespace PointedMatching
variable {a b : List (Letter I)}
def ofStrict {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R) (hr : StrictReduced₂ a R) :
    PointedMatching a b := by
  classical
  let q := (matching_bounded_points hR).choose
  have hq := (matching_bounded_points hR).choose_spec
  let hs := fun n => exists_decorates₂_of_bounded_points a R q
    (fun j hj => (hq j hj).2) (fun j hj => (hq j hj).1) n
  let σ := fun n => (hs n).choose
  have hσ := fun n => (hs n).choose_spec
  exact ⟨R, hR, hr, q, fun j hj => (hq j hj).1, fun j hj => (hq j hj).2, σ,
    fun n => (hσ n).1⟩

@[simp] theorem ofStrict_moves {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a b R) (hr : StrictReduced₂ a R) : (ofStrict hR hr).moves = R := rfl

def layers (F : PointedMatching a b) (n : MatchingStrand a F.moves → ℕ) : List (XLayer I) :=
  dLay a (F.serialize n)

def appendCross {P Q : List (Letter I)} {x y : Letter I}
    (F : PointedMatching a (P ++ x :: y :: Q))
    (hn : ¬ Same (pairing₂ a F.moves) (a.length + P.length) (a.length + P.length + 1))
    (hi : ¬ Ilv (pairing₂ a F.moves) (a.length + P.length)) :
    PointedMatching a (P ++ y :: x :: Q) := by
  let e := terminalCrossStrandEquiv F.matching hn
  refine ⟨F.moves ++ [.mv (.cross P.length)], matching_append_cross a P Q x y F.matching,
    strictReduced_append_cross_of_not_ilv F.matching F.strict hn hi,
    fun j => F.points (tau (a.length + P.length) j), ?_, ?_,
    fun n => F.serialize (n ∘ e) ++ [.tm (.mv (.cross P.length))], ?_⟩
  · intro j hj
    let z : MatchingStrand a F.moves := e.symm ⟨j, hj⟩
    have hz : z.val = tau (a.length + P.length) j := rfl
    have hb := F.bounded z.val z.property
    simp only [List.length_append, List.length_singleton]
    rw [hz] at hb
    omega
  · intro j hj
    let z : MatchingStrand a F.moves := e.symm ⟨j, hj⟩
    have h := onStrand_append_cross F.matching (F.bounded z.val z.property)
      (F.onStrand z.val z.property)
    have hz : z.val = tau (a.length + P.length) j := rfl
    simpa only [hz, tau_tau] using h
  · intro n
    have h := decorates_append_cross_counts F.matching hn F.points (n ∘ e)
      (F.decorates (n ∘ e))
    simpa only [Function.comp_def, e, Equiv.apply_symm_apply] using h

@[simp] theorem appendCross_moves {P Q : List (Letter I)} {x y : Letter I}
    (F : PointedMatching a (P ++ x :: y :: Q))
    (hn : ¬ Same (pairing₂ a F.moves) (a.length + P.length) (a.length + P.length + 1))
    (hi : ¬ Ilv (pairing₂ a F.moves) (a.length + P.length)) :
    (F.appendCross hn hi).moves = F.moves ++ [.mv (.cross P.length)] := rfl

 theorem appendCross_layers {P Q : List (Letter I)} {x y : Letter I}
    (F : PointedMatching a (P ++ x :: y :: Q))
    (hn : ¬ Same (pairing₂ a F.moves) (a.length + P.length) (a.length + P.length + 1))
    (hi : ¬ Ilv (pairing₂ a F.moves) (a.length + P.length))
    (n : MatchingStrand a F.moves → ℕ) :
    (F.appendCross hn hi).layers (n ∘ (terminalCrossStrandEquiv F.matching hn).symm) =
      F.layers n ++ (xCrL x y).map (xwhL P Q) := by
  change dLay a (F.serialize _ ++ _) = _
  have he : (n ∘ (terminalCrossStrandEquiv F.matching hn).symm) ∘
      terminalCrossStrandEquiv F.matching hn = n := by funext j; simp
  rw [he]
  exact dLay_append_terminal_cross F.matching (F.decorates n).1

theorem appendCross_layers_high {P Q : List (Letter I)} {x y : Letter I}
    (F : PointedMatching a (P ++ x :: y :: Q))
    (hn : ¬ Same (pairing₂ a F.moves) (a.length + P.length) (a.length + P.length + 1))
    (hi : ¬ Ilv (pairing₂ a F.moves) (a.length + P.length))
    (n : MatchingStrand a (F.appendCross hn hi).moves → ℕ) :
    (F.appendCross hn hi).layers n =
      F.layers (n ∘ terminalCrossStrandEquiv F.matching hn) ++ (xCrL x y).map (xwhL P Q) :=
  dLay_append_terminal_cross F.matching (F.decorates _).1

end PointedMatching
end OddMath.SKM
