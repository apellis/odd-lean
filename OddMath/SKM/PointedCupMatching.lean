import OddMath.SKM.ContextualCupDecorations

/-! Typed residual-plus-cup serializers as genuine pointed strict matchings. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove
variable {I : Type*}

theorem terminalCupCountsEquiv_symm_apply {a P Q : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (P ++ Q) R) (ε : Bool) (i : I)
    (z : ℕ × (MatchingStrand a R → ℕ))
    (j : MatchingStrand a (R ++ [.mv (.cup P.length (ε, i))])) :
    (terminalCupCountsEquiv hR ε i).symm z j =
      cupCounts a P z.1 (strandCounts z.2) j.val := by
  classical
  change Sum.elim (fun _ => z.1) z.2 (terminalCupStrandEquiv hR ε i j) = _
  by_cases hj : j.val = a.length + P.length
  · dsimp only [terminalCupStrandEquiv, matchingStrandEquivOfCap]
    simp only [Equiv.coe_fn_mk, cupCounts, dite_eq_left hj, ite_eq_left hj, Sum.elim_inl]
  · have hp := cup_inserted_properties a P Q ε i hR
    have hv : Valid (pairing₂ a (R ++ [.mv (.cup P.length (ε, i))])) := by
      rw [pairing_append_cup]; exact hp.1
    have hc : Same (pairing₂ a (R ++ [.mv (.cup P.length (ε, i))]))
        (a.length + P.length) (a.length + P.length + 1) := by
      rw [pairing_append_cup]; exact hp.2.2.2.1
    have hjl := mem_leftEnds₂.mp j.property
    have hn : j.val ≠ a.length + P.length + 1 := by
      intro he
      exact hjl.2 ⟨a.length + P.length, by omega, he ▸ hc.symm⟩
    have hm : capDown (a.length + P.length) j.val ∈ leftEnds₂ a R := by
      have h := (isLeftEnd_rmAt_cap hv hc).mpr
        (show IsLeftEnd (pairing₂ a (R ++ [.mv (.cup P.length (ε, i))]))
          (rmIdx (a.length + P.length) (capDown (a.length + P.length) j.val)) from
            by simpa only [rmIdx_capDown hj hn] using hjl)
      rw [pairing_append_cup, hp.2.2.2.2] at h
      exact mem_leftEnds₂.mpr h
    dsimp only [terminalCupStrandEquiv, matchingStrandEquivOfCap]
    simp only [Equiv.coe_fn_mk, cupCounts, dite_eq_right hj, ite_eq_right hj, Sum.elim_inr,
      strandCounts, dite_eq_left hm]

theorem cupPoints_spec {a P Q : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (P ++ Q) R) (ε : Bool) (i : I) (q : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ a R, (q j).1 ≤ R.length ∧ OnStrand₂ a R j (q j))
    (j : ℕ) (hj : j ∈ leftEnds₂ a (R ++ [.mv (.cup P.length (ε, i))])) :
    (cupPoints a P R ε q j).1 ≤ (R ++ [TMove.mv (.cup P.length (ε, i))]).length ∧
      OnStrand₂ a (R ++ [.mv (.cup P.length (ε, i))]) j (cupPoints a P R ε q j) := by
  let e := terminalCupStrandEquiv hR ε i
  have he := congrArg Subtype.val (e.symm_apply_apply ⟨j, hj⟩)
  cases hz : e ⟨j, hj⟩ with
  | inl u =>
      cases u
      rw [hz] at he
      change a.length + P.length = j at he
      subst j
      simp only [cupPoints, ite_true, List.length_append, List.length_singleton, le_refl, true_and]
      exact onStrand_terminal_cup hR ε i
  | inr z =>
      rw [hz] at he
      change rmIdx (a.length + P.length) z.val = j at he
      subst j
      simp only [cupPoints, ite_eq_right (rmIdx_ne_position _ _), capDown_rmIdx]
      refine ⟨?_, onStrand_append_cup hR ε i (hq z z.property).1 (hq z z.property).2⟩
      have h := (hq z z.property).1
      simp only [List.length_append, List.length_singleton]
      omega

namespace PointedMatching
variable {a P Q : List (Letter I)}

def appendCup (F : PointedMatching a (P ++ Q)) (ε : Bool) (i : I) :
    PointedMatching a (P ++ (ε, i) :: (!ε, i) :: Q) := by
  let e := terminalCupCountsEquiv F.matching ε i
  refine ⟨F.moves ++ [.mv (.cup P.length (ε, i))],
    matching_append_cup a P Q ε i F.matching,
    strictReduced_append_cup F.matching F.strict _ _,
    cupPoints a P F.moves ε F.points, ?_, ?_,
    fun n => cupDecoratedMoves P ε i (e n).1 (F.serialize (e n).2), ?_⟩
  · intro j hj
    exact (cupPoints_spec F.matching ε i F.points
      (fun j hj => ⟨F.bounded j hj, F.onStrand j hj⟩) j hj).1
  · intro j hj
    exact (cupPoints_spec F.matching ε i F.points
      (fun j hj => ⟨F.bounded j hj, F.onStrand j hj⟩) j hj).2
  · intro n
    have hd := decorates_cupDecoratedMoves F.matching ε i (e n).1 (F.decorates (e n).2)
    have he : (fun j : MatchingStrand a (F.moves ++ [.mv (.cup P.length (ε, i))]) =>
        cupCounts a P (e n).1 (strandCounts (e n).2) j.val) = n := by
      funext j
      rw [← terminalCupCountsEquiv_symm_apply F.matching ε i (e n) j]
      exact congrFun (e.symm_apply_apply n) j
    have h := (decorates₂_strandCounts_iff _ _ _).mpr hd
    rw [he] at h
    exact h

@[simp] theorem appendCup_moves (F : PointedMatching a (P ++ Q)) (ε : Bool) (i : I) :
    (F.appendCup ε i).moves = F.moves ++ [.mv (.cup P.length (ε, i))] := rfl

theorem appendCup_layers (F : PointedMatching a (P ++ Q)) (ε : Bool) (i : I)
    (b : ℕ) (n : MatchingStrand a F.moves → ℕ) :
    (F.appendCup ε i).layers ((terminalCupCountsEquiv F.matching ε i).symm (b, n)) =
      F.layers n ++ (xCupL (ε, i)).map (xwhL P Q) ++
      dLay (P ++ (ε, i) :: (!ε, i) :: Q)
        (List.replicate b (.dt (if ε then P.length else P.length + 1))) := by
  change dLay a (cupDecoratedMoves P ε i
    ((terminalCupCountsEquiv F.matching ε i) ((terminalCupCountsEquiv F.matching ε i).symm (b, n))).1
    (F.serialize ((terminalCupCountsEquiv F.matching ε i)
      ((terminalCupCountsEquiv F.matching ε i).symm (b, n))).2)) = _
  rw [Equiv.apply_symm_apply]
  exact dLay_cupDecoratedMoves F.matching ε i b (F.decorates n).1

end PointedMatching
end OddMath.SKM
