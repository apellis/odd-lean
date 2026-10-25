import OddMath.SKM.SourceCapState

/-! Initial source crossing states for contextual sorting in [BE2, Section 8].
The frozen endpoints appear in reverse order. Their initial IDs must be
transposed as well as their positions. -/
namespace OddMath.SKM.SourceCrossState
open StringDiagrams StringDiagrams.Chord
open SourceCapState
variable {I : Type*}

/-- Transpose the two initial IDs selected by the contextual crossing. -/
def exchangeId (q : ℕ) : Equiv.Perm ℕ := Equiv.swap (2 * q) (2 * q + 2)

private theorem indexed_map_fixed (f : ℕ → ℕ) (n : ℕ) (w : List (Letter I))
    (hf : ∀ j, j < w.length → f (n + 2 * j) = n + 2 * j) :
    (indexed n w).map (SourceIdRelabel.idMap f) = indexed n w := by
  apply List.ext_getElem
  · simp
  · intro j h₁ h₂
    simp only [List.getElem_map, indexed, List.getElem_mapIdx, SourceIdRelabel.idMap]
    rw [hf j (by simpa using h₂)]

private theorem before_fixed (L Q : List (Letter I)) :
    (before Q).map (SourceIdRelabel.idMap (exchangeId Q.length)) = before Q ∧
    (after L Q).map (SourceIdRelabel.idMap (exchangeId Q.length)) = after L Q := by
  constructor
  · apply indexed_map_fixed
    intro j hj
    simp only [length_dualW] at hj
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  · apply indexed_map_fixed
    intro j _
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)

/-- Full initial stack, with both selected letters retained. -/
theorem start_st (L Q : List (Letter I)) (x y : Letter I) :
    (tStart (L ++ x :: y :: Q)).st =
      (before Q ++ (2 * Q.length, flipL y) :: (2 * Q.length + 2, flipL x) :: after L Q) ++
      (after L Q).reverse.map flipSnd ++
      (2 * Q.length + 2, x) :: (2 * Q.length, y) ::
      (before Q).reverse.map flipSnd := by
  have he : cupLeft (dualW (L ++ x :: y :: Q)) =
      before Q ++ (2 * Q.length, flipL y) :: (2 * Q.length + 2, flipL x) :: after L Q := by
    rw [show cupLeft (dualW (L ++ x :: y :: Q)) =
      indexed 0 (dualW (L ++ x :: y :: Q)) by simp [cupLeft, indexed]]
    simp only [dualW_append, dualW_cons]
    rw [indexed_append, indexed_append]
    simp [indexed, before, after, length_dualW, Nat.mul_add, Nat.add_assoc]
  simp only [tStart, run_cupMoves, he, List.reverse_append, List.reverse_cons,
    List.map_append, List.map_cons, List.map_nil]
  simp [flipSnd, flipL_flipL, List.append_assoc]

/-- The initial source crossing is always a valid active move. -/
theorem cross_ok (L Q : List (Letter I)) (x y : Letter I) :
    (TMove.mv (.cross L.length)).Ok flipL (L ++ x :: y :: Q).length
      (tStart (L ++ x :: y :: Q)).st := by
  change (L ++ x :: y :: Q).length + L.length + 1 < _
  simp [tStart, run_cupMoves, length_cupLeft, length_dualW]
  omega

/-- Frozen-state transport fixes every fresh ID, including when ID zero moves. -/
theorem fresh (L Q : List (Letter I)) (x y : Letter I) (n : ℕ)
    (hn : (tStart (L ++ x :: y :: Q)).nxt ≤ n) : exchangeId Q.length n = n := by
  simp only [tStart, run_cupMoves, length_cupLeft, length_dualW,
    List.length_append, List.length_cons, List.length_map, List.length_reverse,
    length_cupLeft, length_dualW] at hn
  exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)

/-- Literal layer identification for an initial crossing and every suffix. -/
theorem cross_layers (L Q : List (Letter I)) (x y : Letter I)
    (R : List (TMove (Letter I))) :
    tLay (L ++ x :: y :: Q) (.mv (.cross L.length) :: R) =
      (xCrL x y).map (xwhL L Q) ++ tLay (L ++ y :: x :: Q) R := by
  simp only [tLay, tmLay, moveLay_cross, tLet, chStep_cross]

private theorem map_reverse_flip (f : ℕ → ℕ) (s : List (ℕ × Letter I)) :
    (s.reverse.map flipSnd).map (SourceIdRelabel.idMap f) =
      (s.map (SourceIdRelabel.idMap f)).reverse.map flipSnd := by
  simp only [List.map_reverse, List.map_map]
  rfl

/-- The active endpoints carry the reversed initial IDs. -/
theorem cross_ids (L Q : List (Letter I)) (x y : Letter I) :
    idD (tStart (L ++ x :: y :: Q)).st
        ((L ++ x :: y :: Q).length + L.length) = 2 * Q.length + 2 ∧
    idD (tStart (L ++ x :: y :: Q)).st
        ((L ++ x :: y :: Q).length + L.length + 1) = 2 * Q.length := by
  rw [start_st]
  have hlen : (L ++ x :: y :: Q).length + L.length =
      ((before Q ++ (2 * Q.length, flipL y) :: (2 * Q.length + 2, flipL x) :: after L Q) ++
        (after L Q).reverse.map flipSnd).length := by
    simp [before, after, length_dualW]; omega
  rw [hlen]
  simp only [idD, idAt, List.getElem?_append, List.length_append, List.length_cons,
    List.length_map, List.length_reverse]
  split_ifs <;> simp_all

/-- Exact state after the initial crossing: swap frozen positions and initial
IDs in the swapped-source state, then retain the new crossing in its history. -/
theorem start_cross (L Q : List (Letter I)) (x y : Letter I) :
    tStep flipL (L ++ x :: y :: Q).length (tStart (L ++ x :: y :: Q))
      (.mv (.cross L.length)) =
      { SourceIdRelabel.rename (exchangeId Q.length)
          (SourceFrozenSwap.frozen Q.length (tStart (L ++ y :: x :: Q))) with
        xs := [s(2 * Q.length + 2, 2 * Q.length)] } := by
  have hlen : (L ++ x :: y :: Q).length + L.length =
      ((before Q ++ (2 * Q.length, flipL y) :: (2 * Q.length + 2, flipL x) :: after L Q) ++
        (after L Q).reverse.map flipSnd).length := by
    simp [before, after, length_dualW]; omega
  have hb : (before Q).length = Q.length := by simp [before, length_dualW]
  have hs : ∀ (a b : Letter I), (tStart (L ++ a :: b :: Q)).xs = [] := fun _ _ => rfl
  simp only [tStep]
  rw [(cross_ids L Q x y).1, (cross_ids L Q x y).2]
  simp only [start_st, hs, List.nil_append, SourceIdRelabel.rename,
    SourceFrozenSwap.frozen]
  rw [show (before Q ++ (2 * Q.length, flipL y) :: (2 * Q.length + 2, flipL x) :: after L Q) ++
      (after L Q).reverse.map flipSnd ++
      (2 * Q.length + 2, x) :: (2 * Q.length, y) :: (before Q).reverse.map flipSnd =
    ((before Q ++ (2 * Q.length, flipL y) :: (2 * Q.length + 2, flipL x) :: after L Q) ++
      (after L Q).reverse.map flipSnd) ++
      (2 * Q.length + 2, x) :: (2 * Q.length, y) :: (before Q).reverse.map flipSnd by
        simp [List.append_assoc]]
  rw [hlen, swapAt_mid]
  have hf : swapAt
      ((before Q ++ (2 * Q.length, flipL x) :: (2 * Q.length + 2, flipL y) :: after L Q) ++
        (after L Q).reverse.map flipSnd ++
        (2 * Q.length + 2, y) :: (2 * Q.length, x) :: (before Q).reverse.map flipSnd)
      Q.length =
      before Q ++ (2 * Q.length + 2, flipL y) :: (2 * Q.length, flipL x) ::
        (after L Q ++ (after L Q).reverse.map flipSnd ++
          (2 * Q.length + 2, y) :: (2 * Q.length, x) :: (before Q).reverse.map flipSnd) := by
    simpa only [List.append_assoc, List.cons_append, hb] using
      swapAt_mid (before Q)
        (after L Q ++ (after L Q).reverse.map flipSnd ++
          (2 * Q.length + 2, y) :: (2 * Q.length, x) :: (before Q).reverse.map flipSnd)
        (2 * Q.length, flipL x) (2 * Q.length + 2, flipL y)
  rw [hf]
  simp only [List.map_append, List.map_cons, map_reverse_flip,
    (before_fixed L Q).1, (before_fixed L Q).2]
  simp [SourceIdRelabel.idMap, exchangeId, List.append_assoc,
    tStart, run_cupMoves, length_cupLeft, length_dualW]

/-- Add an earlier crossing history without changing the active state. -/
def history (xs : List (Sym2 ℕ)) (T : TState (Letter I)) : TState (Letter I) :=
  { T with xs := xs ++ T.xs }

private theorem history_step (k : ℕ) (T : TState (Letter I))
    (xs : List (Sym2 ℕ)) (m : TMove (Letter I)) :
    tStep flipL k (history xs T) m =
      history (xs.map (Sym2.map (stepRen k T m))) (tStep flipL k T m) := by
  cases m with
  | mv m => cases m <;> simp [tStep, stepRen, history, List.append_assoc]
  | cap g => simp [tStep, stepRen, history]

/-- Previous crossings do not alter validity of any suffix. -/
theorem history_fits (k : ℕ) (T : TState (Letter I))
    (xs : List (Sym2 ℕ)) (R : List (TMove (Letter I))) :
    TFits flipL k (history xs T) R ↔ TFits flipL k T R := by
  induction R generalizing T xs with
  | nil => rfl
  | cons m R ih =>
    change (m.Ok flipL k T.st ∧ TFits flipL k (tStep flipL k (history xs T) m) R) ↔ _
    rw [history_step, ih]
    rfl

/-- The earlier crossings acquire exactly the cap renaming of the suffix. -/
theorem history_run (k : ℕ) (T : TState (Letter I))
    (xs : List (Sym2 ℕ)) (R : List (TMove (Letter I))) :
    tRun flipL k (history xs T) R =
      history (xs.map (Sym2.map (tRen k T R))) (tRun flipL k T R) := by
  induction R generalizing T xs with
  | nil => simp [tRun, tRen, history]
  | cons m R ih =>
    change tRun flipL k (tStep flipL k (history xs T) m) R = _
    rw [history_step, ih]
    simp only [tRun, List.foldl_cons, tRen, List.map_map, ← Sym2.map_comp]
    rfl

/-- Earlier crossings do not alter distinguished-point IDs. -/
theorem history_ren (k : ℕ) (T : TState (Letter I))
    (xs : List (Sym2 ℕ)) (R : List (TMove (Letter I))) (z : ℕ) :
    tRen k (history xs T) R z = tRen k T R z := by
  induction R generalizing T xs z with
  | nil => rfl
  | cons m R ih =>
    have hs : stepRen k (history xs T) m z = stepRen k T m z := by
      cases m <;> rfl
    simp only [tRen, hs, history_step]
    exact ih _ _ _

/-- Earlier crossings do not alter the critical-ID list. -/
theorem history_crit (k : ℕ) (T : TState (Letter I))
    (xs : List (Sym2 ℕ)) (R : List (TMove (Letter I))) (cl : List ℕ) :
    tCrit flipL k (history xs T) cl R = tCrit flipL k T cl R := by
  induction R generalizing T xs cl with
  | nil => rfl
  | cons m R ih =>
    have hs : critStep k (history xs T) cl m = critStep k T cl m := by
      cases m <;> rfl
    simp only [tCrit, hs, history_step]
    exact ih _ _ _

/-- The state comparison with its earlier crossing history factored out. -/
theorem start_cross_history (L Q : List (Letter I)) (x y : Letter I) :
    tStep flipL (L ++ x :: y :: Q).length (tStart (L ++ x :: y :: Q))
      (.mv (.cross L.length)) =
      history [s(2 * Q.length + 2, 2 * Q.length)]
        (SourceIdRelabel.rename (exchangeId Q.length)
          (SourceFrozenSwap.frozen Q.length (tStart (L ++ y :: x :: Q)))) := by
  rw [start_cross]
  rfl

/-- An arbitrary valid residual word remains valid after the source crossing. -/
theorem cross_fits (L Q : List (Letter I)) (x y : Letter I)
    (R : List (TMove (Letter I)))
    (hR : TFits flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) R) :
    TFits flipL (L ++ x :: y :: Q).length (tStart (L ++ x :: y :: Q))
      (.mv (.cross L.length) :: R) := by
  refine ⟨cross_ok L Q x y, ?_⟩
  rw [start_cross_history, history_fits]
  have hlen : (L ++ x :: y :: Q).length = (L ++ y :: x :: Q).length := by simp
  rw [hlen]
  exact SourceIdRelabel.fits flipL _ (exchangeId Q.length).injective _ (SourceFrozenSwap.frozen Q.length (tStart (L ++ y :: x :: Q)))
    (fun n hn => fresh L Q y x n hn) R (SourceFrozenSwap.fits flipL (p := Q.length) (by simp) _ _ hR)

/-- Actual post-crossing critical IDs are the transposed residual IDs. -/
theorem cross_crit (L Q : List (Letter I)) (x y : Letter I)
    (R : List (TMove (Letter I)))
    (hR : TFits flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) R) :
    tCrit flipL (L ++ x :: y :: Q).length (tStart (L ++ x :: y :: Q)) []
      (.mv (.cross L.length) :: R) =
      (tCrit flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) [] R).map
        (exchangeId Q.length) := by
  change tCrit flipL _ (tStep flipL _ _ _) [] R = _
  rw [start_cross_history, history_crit]
  have hlen : (L ++ x :: y :: Q).length = (L ++ y :: x :: Q).length := by simp
  rw [hlen]
  have hF := SourceFrozenSwap.fits flipL (p := Q.length) (by simp) _ _ hR
  have H := SourceIdRelabel.crit flipL _ (exchangeId Q.length).injective _ (SourceFrozenSwap.frozen Q.length (tStart (L ++ y :: x :: Q)))
    (fun n hn => fresh L Q y x n hn) R hF []
  rw [List.map_nil] at H
  rw [H, SourceFrozenSwap.crit flipL (by simp) _ _ hR []]

/-- Distinguished-point IDs acquire precisely the initial source transposition. -/
theorem cross_ren (L Q : List (Letter I)) (x y : Letter I)
    (R : List (TMove (Letter I)))
    (hR : TFits flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) R)
    (z : ℕ) :
    tRen (L ++ x :: y :: Q).length (tStart (L ++ x :: y :: Q))
      (.mv (.cross L.length) :: R) (exchangeId Q.length z) =
      exchangeId Q.length (tRen (L ++ y :: x :: Q).length
        (tStart (L ++ y :: x :: Q)) R z) := by
  change tRen _ (tStep flipL _ _ _) R (exchangeId Q.length z) = _
  rw [start_cross_history, history_ren]
  have hlen : (L ++ x :: y :: Q).length = (L ++ y :: x :: Q).length := by simp
  rw [hlen]
  have hF := SourceFrozenSwap.fits flipL (p := Q.length) (by simp) _ _ hR
  rw [SourceIdRelabel.ren _ (exchangeId Q.length).injective _ (SourceFrozenSwap.frozen Q.length (tStart (L ++ y :: x :: Q))) (fun n hn => fresh L Q y x n hn) R hF z,
    SourceFrozenSwap.ren (by simp) _ _ hR z]

/-- Full state transport retains the initial crossing after all cap renamings.
In particular, it is not enough to compare only the terminal pairing. -/
theorem cross_run (L Q : List (Letter I)) (x y : Letter I)
    (R : List (TMove (Letter I)))
    (hR : TFits flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) R) :
    tRun flipL (L ++ x :: y :: Q).length (tStart (L ++ x :: y :: Q))
      (.mv (.cross L.length) :: R) =
      history [s(exchangeId Q.length (tRen (L ++ y :: x :: Q).length
          (tStart (L ++ y :: x :: Q)) R (2 * Q.length)),
        exchangeId Q.length (tRen (L ++ y :: x :: Q).length
          (tStart (L ++ y :: x :: Q)) R (2 * Q.length + 2)))]
        (SourceIdRelabel.rename (exchangeId Q.length)
          (SourceFrozenSwap.frozen Q.length
            (tRun flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) R))) := by
  change tRun flipL _ (tStep flipL _ _ _) R = _
  rw [start_cross_history, history_run]
  have hlen : (L ++ x :: y :: Q).length = (L ++ y :: x :: Q).length := by simp
  rw [hlen]
  have hF := SourceFrozenSwap.fits flipL (p := Q.length) (by simp) _ _ hR
  rw [SourceIdRelabel.run flipL _ (exchangeId Q.length).injective _ (SourceFrozenSwap.frozen Q.length (tStart (L ++ y :: x :: Q)))
    (fun n hn => fresh L Q y x n hn) R hF, SourceFrozenSwap.run flipL (by simp) _ _ hR]
  have h₁ : exchangeId Q.length (2 * Q.length) = 2 * Q.length + 2 := by simp [exchangeId]
  have h₂ : exchangeId Q.length (2 * Q.length + 2) = 2 * Q.length := by simp [exchangeId]
  have hren (z : ℕ) := SourceIdRelabel.ren _ (exchangeId Q.length).injective _
    (SourceFrozenSwap.frozen Q.length (tStart (L ++ y :: x :: Q)))
    (fun n hn => fresh L Q y x n hn) R hF z
  have hr₁ := hren (2 * Q.length)
  have hr₂ := hren (2 * Q.length + 2)
  rw [h₁, SourceFrozenSwap.ren (by simp) _ _ hR] at hr₁
  rw [h₂, SourceFrozenSwap.ren (by simp) _ _ hR] at hr₂
  simp only [List.map_cons, List.map_nil, Sym2.map_mk, hr₁, hr₂]

end OddMath.SKM.SourceCrossState
