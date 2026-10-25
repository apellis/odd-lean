import OddMath.SKM.CupAttachmentReduced

/-! # Literal right-target cap attachment

Move a final upward target endpoint to a final downward source endpoint.
The outer strand is represented by a fresh ID 0; old IDs are shifted by 2.
-/
namespace OddMath.SKM.RightCapAttachment
open StringDiagrams StringDiagrams.Chord DTMove
variable {I : Type*}

def liftId (z : ℕ × Letter I) : ℕ × Letter I := (z.1 + 2, z.2)

def frame (x : Letter I) (T : TState (Letter I)) : TState (Letter I) :=
  ⟨T.nxt + 2, (0, flipL x) :: T.st.map liftId ++ [(0, x)],
    T.xs.map (Sym2.map (fun n => n + 2))⟩

private theorem insAt_right {α : Type*} (s : List α) (z A B : α) {r : ℕ}
    (hr : r ≤ s.length) :
    insAt (s ++ [z]) r A B = insAt s r A B ++ [z] := by
  simp only [insAt, List.take_append_of_le_length hr, List.drop_append_of_le_length hr]
  simp [List.append_assoc]

private theorem rmAt_right {α : Type*} (s : List α) (z : α) {r : ℕ}
    (hr : r + 2 ≤ s.length) :
    rmAt (s ++ [z]) r = rmAt s r ++ [z] := by
  simp only [rmAt, List.take_append_of_le_length (show r ≤ s.length by omega),
    List.drop_append_of_le_length hr, List.append_assoc]

private theorem swapAt_right (s : List (ℕ × Letter I)) (z : ℕ × Letter I) {r : ℕ}
    (hr : r + 1 < s.length) :
    swapAt (s ++ [z]) r = swapAt s r ++ [z] := by
  obtain ⟨P, A, B, Q, hs, hP⟩ := exists_mid hr
  subst hs
  subst hP
  simp [swapAt, List.append_assoc]

private theorem idD_frame (x : Letter I) (T : TState (Letter I)) {r : ℕ}
    (hr : r < T.st.length) :
    idD (frame x T).st (r + 1) = idD T.st r + 2 := by
  simp only [frame, List.cons_append, idD, idAt, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simpa using hr), List.getElem?_map,
    List.getElem?_eq_getElem hr]
  rfl

private theorem rlId_add_two (x y z : ℕ) :
    rlId (x + 2) (y + 2) (z + 2) = rlId x y z + 2 := by
  simp only [rlId, Nat.add_right_cancel_iff]
  split_ifs <;> rfl

private theorem insAt_frame (x : Letter I) (T : TState (Letter I))
    {r : ℕ} (hr : r ≤ T.st.length) (A B : ℕ × Letter I) :
    insAt (frame x T).st (r + 1) (liftId A) (liftId B) =
      (0, flipL x) :: (insAt T.st r A B).map liftId ++ [(0, x)] := by
  rw [Nat.add_comm r 1]
  change insAt ([(0, flipL x)] ++ (T.st.map liftId ++ [(0, x)])) ([(0, flipL x)].length + r) _ _ = _
  rw [insAt_append_left, insAt_right _ _ _ _ (by simpa using hr), ← map_insAt]
  rfl

private theorem swapAt_frame (x : Letter I) (T : TState (Letter I))
    {r : ℕ} (hr : r + 1 < T.st.length) :
    swapAt (frame x T).st (r + 1) =
      (0, flipL x) :: (swapAt T.st r).map liftId ++ [(0, x)] := by
  rw [Nat.add_comm r 1]
  change swapAt ([(0, flipL x)] ++ (T.st.map liftId ++ [(0, x)])) ([(0, flipL x)].length + r) = _
  rw [swapAt_append_left _ _ (by simp; omega),
    swapAt_right _ _ (by simpa using hr), ← map_swapAt]
  rfl

private theorem jn_frame (x : Letter I) (T : TState (Letter I))
    {r : ℕ} (hr : r + 1 < T.st.length) :
    jn (frame x T).st (r + 1) =
      (0, flipL x) :: (jn T.st r).map liftId ++ [(0, x)] := by
  obtain ⟨P, A, B, Q, hs, hP⟩ := exists_mid hr
  have hm : (frame x T).st = ((0, flipL x) :: P.map liftId) ++
      [liftId A, liftId B] ++ (Q.map liftId ++ [(0, x)]) := by
    simp [frame, hs, List.append_assoc]
  have hn : r + 1 = ((0, flipL x) :: P.map liftId).length := by simp; omega
  rw [hm, hn, jn_mid, hs, ← hP, jn_mid]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map]
  have he : (fun z : ℕ × Letter I => rl (liftId B).1 (liftId A).1 (liftId z)) =
      (fun z => liftId (rl B.1 A.1 z)) := by
    funext z
    exact Prod.ext (rlId_add_two B.1 A.1 z.1) rfl
  simp only [Function.comp_def] at *
  rw [he]
  simp [rl, rlId, liftId, List.append_assoc]

private theorem state_ext {T U : TState (Letter I)} (hn : T.nxt = U.nxt)
    (hs : T.st = U.st) (hx : T.xs = U.xs) : T = U := by
  cases T
  cases U
  cases hn
  cases hs
  cases hx
  rfl

/-- Running an old move between the two outer endpoints commutes with framing. -/
theorem frame_step (x : Letter I) (k : ℕ) (T : TState (Letter I))
    (m : TMove (Letter I)) (hm : m.Ok flipL k T.st) :
    tStep flipL (k + 1) (frame x T) m = frame x (tStep flipL k T m) := by
  rcases m with (⟨g, y⟩ | p) | g
  · apply state_ext
    · simp only [tStep, frame, Nat.add_right_comm]
    · change insAt (frame x T).st (k + 1 + g) (liftId (T.nxt, y))
        (liftId (T.nxt, flipL y)) = _
      rw [show k + 1 + g = (k + g) + 1 by omega, insAt_frame x T hm]
      rfl
    · rfl
  · have hr : k + p + 1 < T.st.length := hm
    apply state_ext
    · rfl
    · change swapAt (frame x T).st (k + 1 + p) = _
      rw [show k + 1 + p = (k + p) + 1 by omega, swapAt_frame x T hm]
      rfl
    · change (frame x T).xs ++ [s(idD (frame x T).st (k + 1 + p),
        idD (frame x T).st (k + 1 + p + 1))] = _
      rw [show k + 1 + p = (k + p) + 1 by omega,
        idD_frame x T (show k + p < T.st.length by omega), idD_frame x T hr]
      simp [frame, tStep]
  · have hr : k + g + 1 < T.st.length := by
      obtain ⟨A, B, hA, hB, hdual, hne⟩ := hm
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hB
      cases hB
    apply state_ext
    · rfl
    · change jn (frame x T).st (k + 1 + g) = _
      rw [show k + 1 + g = (k + g) + 1 by omega, jn_frame x T hr]
      rfl
    · change ((frame x T).xs.map (Sym2.map
        (rlId (idD (frame x T).st (k + 1 + g + 1))
          (idD (frame x T).st (k + 1 + g))))) = _
      rw [show k + 1 + g = (k + g) + 1 by omega,
        idD_frame x T hr, idD_frame x T (show k + g < T.st.length by omega)]
      simp only [frame, tStep, List.map_map]
      apply List.map_congr_left
      intro z _
      simp only [Function.comp_apply, Sym2.map_map]
      congr 1
      funext n
      exact rlId_add_two _ _ n

private theorem getElem_frame (x : Letter I) (T : TState (Letter I)) {r : ℕ}
    (hr : r < T.st.length) :
    (frame x T).st[r + 1]? = (T.st[r]?).map liftId := by
  simp only [frame, List.cons_append, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by simpa using hr), List.getElem?_map]

/-- Framing adds no obstruction to an old valid move. -/
theorem frame_ok (x : Letter I) (k : ℕ) (T : TState (Letter I))
    (m : TMove (Letter I)) (hm : m.Ok flipL k T.st) :
    m.Ok flipL (k + 1) (frame x T).st := by
  rcases m with (⟨g, y⟩ | p) | g
  · change k + 1 + g ≤ (frame x T).st.length
    have h : k + g ≤ T.st.length := hm
    simp only [frame, List.length_append, List.length_cons, List.length_map]
    omega
  · change k + 1 + p + 1 < (frame x T).st.length
    have h : k + p + 1 < T.st.length := hm
    simp only [frame, List.length_append, List.length_cons, List.length_map]
    omega
  · obtain ⟨A, B, hA, hB, hdual, hne⟩ := hm
    have hr : k + g + 1 < T.st.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hB
      cases hB
    refine ⟨liftId A, liftId B, ?_, ?_, hdual, ?_⟩
    · rw [show k + 1 + g = (k + g) + 1 by omega,
        getElem_frame x T (by omega), hA]
      rfl
    · rw [show k + 1 + g + 1 = (k + g + 1) + 1 by omega,
        getElem_frame x T hr, hB]
      rfl
    · exact fun h => hne (Nat.add_right_cancel h)

/-- The complete right-whiskered run has exactly the framed state and crossing IDs. -/
theorem frame_run (x : Letter I) (k : ℕ) (T : TState (Letter I))
    (R : List (TMove (Letter I))) (hR : TFits flipL k T R) :
    TFits flipL (k + 1) (frame x T) R ∧
      tRun flipL (k + 1) (frame x T) R = frame x (tRun flipL k T R) := by
  induction R generalizing T with
  | nil => exact ⟨trivial, rfl⟩
  | cons m R ih =>
    obtain ⟨hf, hs⟩ := ih (tStep flipL k T m) hR.2
    refine ⟨⟨frame_ok x k T m hR.1, ?_⟩, ?_⟩
    · rw [frame_step x k T m hR.1]
      exact hf
    · simpa only [tRun, List.foldl_cons, frame_step x k T m hR.1] using hs

private theorem cupLeft_cons_frame (x : Letter I) (w : List (Letter I)) :
    cupLeft (x :: w) = (0, x) :: (cupLeft w).map liftId := by
  unfold cupLeft
  rw [List.mapIdx_cons]
  simp only [Nat.mul_zero, List.mapIdx_eq_zipIdx_map, List.map_map]
  congr 1

/-- Appending a bottom endpoint creates the exact fresh outer pair frame. -/
theorem frame_start (x : Letter I) (a : List (Letter I)) :
    tStart (a ++ [x]) = frame x (tStart a) := by
  have hb : dualW (a ++ [x]) = flipL x :: dualW a := by
    simp only [dualW_append, dualW_cons, dualW_nil, List.nil_append, List.singleton_append]
  apply state_ext
  · simp only [tStart, frame, run_cupMoves, List.length_append, List.length_map,
      List.length_reverse, length_cupLeft, length_dualW, List.length_singleton]
    omega
  · simp only [tStart, hb, run_cupMoves, cupLeft_cons_frame, List.reverse_cons,
      List.map_append, List.map_cons, List.map_nil, List.map_reverse, List.map_map,
      frame, List.cons_append]
    simp [flipSnd, flipL, liftId, List.append_assoc, Function.comp_def]
  · rfl

/-- The final cap closes the fresh outer strand against the last old endpoint.
It moves that endpoint to the front and leaves the shifted crossing list intact. -/
theorem frame_cap_end (x : Letter I) (T : TState (Letter I))
    (P : List (ℕ × Letter I)) (q : ℕ) (hs : T.st = P ++ [(q, flipL x)]) :
    (TMove.cap (P.length + 1)).Ok flipL 0 (frame x T).st ∧
      (tStep flipL 0 (frame x T) (.cap (P.length + 1))).st =
        (q + 2, flipL x) :: P.map liftId ∧
      (tStep flipL 0 (frame x T) (.cap (P.length + 1))).xs =
        T.xs.map (Sym2.map (fun n => n + 2)) := by
  let U := (0, flipL x) :: P.map liftId
  have hU : U.length = P.length + 1 := by simp [U]
  have hst : (frame x T).st = U ++ [(q + 2, flipL x), (0, x)] := by
    simp [frame, hs, U, liftId, List.append_assoc]
  have hA : (frame x T).st[P.length + 1]? = some (q + 2, flipL x) := by
    rw [hst, ← hU]
    simp
  have hB : (frame x T).st[P.length + 1 + 1]? = some (0, x) := by
    rw [hst, ← hU]
    simp
  refine ⟨⟨(q + 2, flipL x), (0, x), by simpa only [Nat.zero_add] using hA,
      by simpa only [Nat.zero_add] using hB, rfl, by omega⟩, ?_, ?_⟩
  · change jn (frame x T).st (0 + (P.length + 1)) = _
    rw [Nat.zero_add, hst, ← hU]
    have hj := jn_mid U [] (q + 2, flipL x) (0, x)
    simp only [List.append_nil] at hj
    rw [hj]
    simp [U, rl, rlId, liftId, List.map_map, Function.comp_def]
  · change (frame x T).xs.map (Sym2.map
        (rlId (idD (frame x T).st (0 + (P.length + 1) + 1))
          (idD (frame x T).st (0 + (P.length + 1))))) = _
    simp only [Nat.zero_add, idD, idAt, hA, hB, Option.map_some, Option.getD_some]
    change (T.xs.map (Sym2.map (fun n => n + 2))).map (Sym2.map (rlId 0 (q + 2))) = _
    simp only [List.map_map, ← Sym2.map_comp]
    congr 1

/-- Right whiskering requires no index change in the original move list. -/
def attach (b : List (Letter I)) (R : List (TMove (Letter I))) : List (TMove (Letter I)) :=
  R ++ [.cap b.length]

/-- The full attached matching and its exact cyclic endpoint/crossing description. -/
theorem attach_matching_state {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R) :
    IsMatching₂ (a ++ [x]) b (attach b R) ∧
    ∃ (P : List (ℕ × Letter I)) (q : ℕ),
      pairing₂ a R = P ++ [(q, flipL x)] ∧
      pairing₂ (a ++ [x]) (attach b R) = (q + 2, flipL x) :: P.map liftId ∧
      (tRun flipL (a ++ [x]).length (tStart (a ++ [x])) (attach b R)).xs =
        (tRun flipL a.length (tStart a) R).xs.map (Sym2.map (fun n => n + 2)) := by
  let T := tRun flipL a.length (tStart a) R
  have hletters := hR.pairing_properties.2.2
  rw [← List.append_assoc] at hletters
  obtain ⟨P, Q, hs, hP, hQ⟩ := List.map_eq_append_iff.mp hletters
  obtain ⟨⟨q, y⟩, rfl, rfl⟩ := List.map_eq_singleton_iff.mp hQ
  have hlen : P.length = a.length + b.length := by
    have h := congrArg List.length hP
    simpa only [List.length_map, List.length_append, length_dualW] using h
  have hrun := frame_run x a.length (tStart a) R hR.1
  have hinit : TFits flipL (a ++ [x]).length (tStart (a ++ [x])) R := by
    simpa only [List.length_append, List.length_singleton, frame_start] using hrun.1
  have hstate : tRun flipL (a ++ [x]).length (tStart (a ++ [x])) R = frame x T := by
    simpa only [List.length_append, List.length_singleton, frame_start] using hrun.2
  have hc := frame_cap_end x T P q hs
  have hidx : (a ++ [x]).length + b.length = P.length + 1 := by simp; omega
  have hcap : (TMove.cap b.length).Ok flipL (a ++ [x]).length (frame x T).st := by
    simpa only [TMove.Ok, Nat.zero_add, hidx] using hc.1
  have hf : TFits flipL (a ++ [x]).length (tStart (a ++ [x])) (attach b R) := by
    apply (tFits_append_at _ _ _ _).mpr
    exact ⟨hinit, by rw [hstate]; exact ⟨hcap, trivial⟩⟩
  have he : tRun flipL (a ++ [x]).length (tStart (a ++ [x])) (attach b R) =
      tStep flipL 0 (frame x T) (.cap (P.length + 1)) := by
    change tRun flipL (a ++ [x]).length (tStart (a ++ [x])) (R ++ [.cap b.length]) = _
    simp only [tRun, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change tStep flipL _ (tRun flipL _ _ R) (.cap b.length) = _
    rw [hstate]
    simp only [tStep, hidx, Nat.zero_add]
  have hfinal : pairing₂ (a ++ [x]) (attach b R) = (q + 2, flipL x) :: P.map liftId := by
    change (tRun flipL _ _ _).st = _
    rw [he]
    exact hc.2.1
  refine ⟨⟨hf, ?_⟩, P, q, hs, hfinal, ?_⟩
  · have h := letters_tRun (length_dualW (a ++ [x])) (attach b R)
      (tStart (a ++ [x])) (a ++ [x]) (tStart_letters _) hf
    change (pairing₂ (a ++ [x]) (attach b R)).map Prod.snd = _ at h
    rw [hfinal] at h
    have hb : dualW (a ++ [x]) = flipL x :: dualW a := by
      simp only [dualW_append, dualW_cons, dualW_nil, List.nil_append, List.singleton_append]
    simp only [List.map_cons, List.map_map, liftId, Function.comp_def] at h
    rw [hP, hb] at h
    exact List.append_cancel_left (List.cons.inj h).2.symm
  · rw [he]
    exact hc.2.2

theorem attach_matching {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R) :
    IsMatching₂ (a ++ [x]) b (attach b R) := (attach_matching_state hR).1

/-- The cyclic boundary correspondence, retaining the actual endpoint ID relabeling. -/
theorem attach_pairing_iso {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R) :
    ∃ (P : List (ℕ × Letter I)) (q : ℕ), pairing₂ a R = P ++ [(q, flipL x)] ∧
      Iso (pairing₂ (a ++ [x]) (attach b R)) ((q, flipL x) :: P) := by
  obtain ⟨_, P, q, hs, hp, _⟩ := attach_matching_state hR
  refine ⟨P, q, hs, ?_⟩
  rw [hp]
  exact iso_map_of_injOn ((q, flipL x) :: P) (fun n => n + 2)
    (fun _ _ _ _ h => Nat.add_right_cancel h)

/-- Literal right-target cap attachment preserves weak reducedness, directly
from the injective relabeling of the actual crossing list. -/
theorem attach_reduced {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R)
    (hred : Reduced₂ a R) : Reduced₂ (a ++ [x]) (attach b R) := by
  obtain ⟨_, P, q, hs, hp, hx⟩ := attach_matching_state hR
  unfold Reduced₂
  rw [hx]
  have hi : Function.Injective (fun n : ℕ => n + 2) := fun _ _ h => Nat.add_right_cancel h
  refine ⟨hred.1.map (Sym2.map.injective hi), ?_⟩
  intro z hz
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
  exact fun hd => hred.2 w hw ((Sym2.isDiag_map hi).mp hd)

@[simp] theorem ncr_attach (b : List (Letter I)) (R : List (TMove (Letter I))) :
    ncr₂ (attach b R) = ncr₂ R := by simp [attach, ncr₂]

end OddMath.SKM.RightCapAttachment
