import OddMath.SKM.SpanReducedMatchings

/-! Frozen source-endpoint transpositions commute with every subsequent
matching move. This is the state transport needed for literal source crossing
attachment in contextual sorting (SKM Section 8). -/
namespace OddMath.SKM.SourceFrozenSwap
open StringDiagrams StringDiagrams.Chord
variable {α : Type*}

def frozen (p : ℕ) (T : TState α) : TState α :=
  ⟨T.nxt, swapAt T.st p, T.xs⟩

private theorem get_swap_right (s : List α) {p r : ℕ}
    (h : p + 2 ≤ r) (hr : r < s.length) : (swapAt s p)[r]? = s[r]? := by
  rw [getElem?_swapAt _ (by omega), tau_of_ne (by omega) (by omega)]

private theorem idD_swap_right (s : List (ℕ × α)) {p r : ℕ}
    (h : p + 2 ≤ r) (hr : r < s.length) : idD (swapAt s p) r = idD s r := by
  simp only [idD, idAt, get_swap_right s h hr]

private theorem jn_eq_map (s : List (ℕ × α)) {r : ℕ} (hr : r + 1 < s.length) :
    jn s r = (rmAt s r).map (rl (idD s (r + 1)) (idD s r)) := by
  obtain ⟨P, A, B, Q, rfl, rfl⟩ := exists_mid hr
  rw [jn_mid, rmAt_mid]
  simp [idD, idAt]

private theorem jn_swap_right (s : List (ℕ × α)) {p r : ℕ}
    (h : p + 2 ≤ r) (hr : r + 1 < s.length) :
    jn (swapAt s p) r = swapAt (jn s r) p := by
  rw [jn_eq_map _ (by simpa using hr), jn_eq_map _ hr,
    idD_swap_right s (by omega) hr, idD_swap_right s h (by omega),
    rmAt_swapAt s (Or.inl ⟨h, rfl⟩) (by omega) (by omega), map_swapAt]

/-- A frozen endpoint swap does not affect validity of an active move. -/
theorem ok (d : α → α) {k p : ℕ} (hpk : p + 2 ≤ k)
    (T : TState α) (m : TMove α) (hm : m.Ok d k T.st) :
    m.Ok d k (frozen p T).st := by
  cases m with
  | mv m => cases m <;> simpa [TMove.Ok, frozen] using hm
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have hr : k + g + 1 < T.st.length := List.getElem?_eq_some_iff.mp hB |>.1
    exact ⟨A, B, (get_swap_right T.st (by omega) (by omega)).trans hA,
      (get_swap_right T.st (by omega) hr).trans hB, hl, hn⟩

/-- Literal active state evolution commutes with a frozen source swap,
including cap ID renaming and the complete crossing list. -/
theorem step (d : α → α) {k p : ℕ} (hpk : p + 2 ≤ k)
    (T : TState α) (m : TMove α) (hm : m.Ok d k T.st) :
    tStep d k (frozen p T) m = frozen p (tStep d k T m) := by
  cases m with
  | mv m =>
    cases m with
    | cup g a =>
      simp only [tStep, frozen]
      rw [insAt_swapAt_lt T.st (by omega) hm]
    | cross r =>
      simp only [tStep, frozen]
      have hr : k + r + 1 < T.st.length := hm
      rw [swapAt_comm T.st (by omega) hr,
        idD_swap_right T.st (by omega) (by omega),
        idD_swap_right T.st (by omega) hr]
  | cap g =>
    obtain ⟨A, B, hA, hB, hl, hn⟩ := hm
    have hr : k + g + 1 < T.st.length := List.getElem?_eq_some_iff.mp hB |>.1
    simp only [tStep, frozen]
    change TState.mk _ (jn (swapAt T.st p) _) _ =
      TState.mk _ (swapAt (jn T.st _) p) _
    rw [jn_swap_right T.st (by omega) hr,
      idD_swap_right T.st (by omega) hr, idD_swap_right T.st (by omega) (by omega)]

/-- Every subsequent move remains valid after the frozen transposition. -/
theorem fits (d : α → α) {k p : ℕ} (hpk : p + 2 ≤ k)
    (T : TState α) (R : List (TMove α)) (hR : TFits d k T R) :
    TFits d k (frozen p T) R := by
  induction R generalizing T with
  | nil => trivial
  | cons m R ih =>
    refine ⟨ok d hpk T m hR.1, ?_⟩
    rw [step d hpk T m hR.1]
    exact ih _ hR.2

/-- The same transport holds for an arbitrary finite valid matching word. -/
theorem run (d : α → α) {k p : ℕ} (hpk : p + 2 ≤ k)
    (T : TState α) (R : List (TMove α)) (hR : TFits d k T R) :
    tRun d k (frozen p T) R = frozen p (tRun d k T R) := by
  induction R generalizing T with
  | nil => rfl
  | cons m R ih =>
    change tRun d k (tStep d k (frozen p T) m) R =
      frozen p (tRun d k (tStep d k T m) R)
    rw [step d hpk T m hR.1]
    exact ih _ hR.2

end OddMath.SKM.SourceFrozenSwap
