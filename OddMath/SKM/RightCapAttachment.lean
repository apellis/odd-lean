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

private theorem tmLay_right (v : List (Letter I)) {l : List (Letter I)}
    {m : TMove (Letter I)} (hm : LOk l m) :
    tmLay (l ++ v) m = (tmLay l m).map (xwhL [] v) ∧
      tLet (l ++ v) m = tLet l m ++ v := by
  cases m with
  | mv m =>
    have h := moveLay_shift [] v (show m.Ok l.length from hm)
    cases m <;> simpa only [shiftM, List.length_nil, Nat.zero_add, List.nil_append, tmLay, tLet] using h
  | cap g =>
    obtain ⟨P, y, Q, rfl, rfl⟩ := hm
    have he : (P ++ flipL y :: y :: Q) ++ v = P ++ flipL y :: y :: (Q ++ v) := by simp
    rw [he, (tmLay_cap P (Q ++ v) (flipL y) y).1,
      (tmLay_cap P Q (flipL y) y).1,
      (tmLay_cap P (Q ++ v) (flipL y) y).2,
      (tmLay_cap P Q (flipL y) y).2, map_xwhL_xwhL]
    simp

private theorem dotOn_right (v : List (Letter I)) {l : List (Letter I)} {p : ℕ}
    (hp : p < l.length) : dotOn (l ++ v) p = (dotOn l p).map (xwhL [] v) := by
  obtain ⟨P, y, Q, rfl, rfl⟩ := exists_split_dot hp
  have he : (P ++ y :: Q) ++ v = P ++ y :: (Q ++ v) := by simp
  rw [he, dotOn_eq, dotOn_eq, map_xwhL_xwhL]
  simp

private theorem lOk_at {k : ℕ} {u l : List (Letter I)} {T : TState (Letter I)}
    (hu : u.length = k) (hl : T.st.map Prod.snd = u ++ l)
    {m : TMove (Letter I)} (hm : m.Ok flipL k T.st) : LOk l m := by
  have hm' : (shiftT u.length m).Ok flipL 0 T.st := by
    rcases m with (⟨g, y⟩ | p) | g <;> simpa only [shiftT, shiftM, TMove.Ok, Nat.zero_add, hu] using hm
  exact lOk_unshift u (lOk_of_ok hl hm')

/-- Right whiskering preserves the actual decorated layers, including cap moves
and dots, provided the dots occupy existing strands. -/
theorem dLay_right {k : ℕ} {u : List (Letter I)} (hu : u.length = k)
    (v : List (Letter I)) (ds : List (DTMove I)) (T : TState (Letter I))
    (l : List (Letter I)) (hl : T.st.map Prod.snd = u ++ l)
    (hf : TFits flipL k T (tmoves ds)) (hd : DOk₂ l ds) :
    dLay (l ++ v) ds = (dLay l ds).map (xwhL [] v) ∧
      (tmoves ds).foldl tLet (l ++ v) = (tmoves ds).foldl tLet l ++ v := by
  induction ds generalizing T l with
  | nil => exact ⟨rfl, rfl⟩
  | cons d ds ih =>
    cases d with
    | tm m =>
      obtain ⟨hm, hf⟩ := hf
      have hm' := lOk_at hu hl hm
      have hn := letters_tRun hu [m] T l hl ⟨hm, trivial⟩
      simp only [tRun, List.foldl_cons, List.foldl_nil] at hn
      obtain ⟨he, ht⟩ := tmLay_right v hm'
      obtain ⟨hds, hfold⟩ := ih _ _ hn hf hd
      simp only [dLay, tmoves, List.foldl_cons, ht, he, hds, hfold, List.map_append, and_self]
    | dt p =>
      obtain ⟨hds, hfold⟩ := ih _ _ hl hf hd.2
      simp only [dLay, tmoves, dotOn_right v hd.1, hds, hfold, List.map_append, and_self]

/-- Attach the actual cap to a decorated move list; all original dot positions remain. -/
def attachMoves (b : List (Letter I)) (ds : List (DTMove I)) : List (DTMove I) :=
  ds ++ [.tm (.cap b.length)]

@[simp] theorem tmoves_attachMoves (b : List (Letter I)) (ds : List (DTMove I)) :
    tmoves (attachMoves b ds) = attach b (tmoves ds) := by simp [attachMoves, attach, tmoves]

/-- The cap attachment agrees literally with right-whiskering the old decorated
layers and appending the corresponding cap; no normalization is involved. -/
theorem dLay_attachMoves {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R)
    {ds : List (DTMove I)} (hm : tmoves ds = R) (hd : DOk₂ a ds) :
    dLay (a ++ [x]) (attachMoves b ds) =
      (dLay a ds).map (xwhL [] [x]) ++ (xCapL x).map (xwhL b []) := by
  obtain ⟨hlay, hfold⟩ := dLay_right (length_dualW a) [x] ds (tStart a) a
    (tStart_letters a) (by rw [hm]; exact hR.1) hd
  rw [attachMoves, dLay_append, hlay, hfold, hm, hR.2]
  have he : (b ++ [flipL x]) ++ [x] = b ++ flipL x :: x :: [] := by simp
  simp only [dLay, List.append_nil]
  rw [he, (tmLay_cap b [] (flipL x) x).1]

@[simp] theorem dotPts_attachMoves (b : List (Letter I)) (ds : List (DTMove I)) :
    dotPts (attachMoves b ds) = dotPts ds := by
  unfold attachMoves
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    cases d <;> simp only [List.cons_append, dotPts, ih]

/-- The strand-renaming function of a framed run is the old one shifted by two. -/
theorem frame_ren (x : Letter I) (k : ℕ) (T : TState (Letter I))
    (R : List (TMove (Letter I))) (hR : TFits flipL k T R) (n : ℕ) :
    tRen (k + 1) (frame x T) R (n + 2) = tRen k T R n + 2 := by
  induction R generalizing T n with
  | nil => rfl
  | cons m R ih =>
    have hs : stepRen (k + 1) (frame x T) m (n + 2) = stepRen k T m n + 2 := by
      cases m with
      | mv m => rfl
      | cap g =>
        have hr : k + g + 1 < T.st.length := by
          obtain ⟨A, B, hA, hB, hdual, hne⟩ := hR.1
          by_contra h
          rw [List.getElem?_eq_none (by omega)] at hB
          cases hB
        simp only [stepRen]
        rw [show k + 1 + g = (k + g) + 1 by omega, idD_frame x T hr,
          idD_frame x T (show k + g < T.st.length by omega)]
        exact rlId_add_two _ _ n
    simp only [tRen, hs, frame_step x k T m hR.1]
    exact ih _ hR.2 _

private theorem tRen_append_at (k : ℕ) (T : TState (Letter I))
    (R S : List (TMove (Letter I))) (n : ℕ) :
    tRen k T (R ++ S) n = tRen k (tRun flipL k T R) S (tRen k T R n) := by
  induction R generalizing T n with
  | nil => rfl
  | cons m R ih => exact ih _ _

private theorem idD_lEnd {s : List (ℕ × Letter I)} {i : ℕ} (hi : i < s.length) :
    idD s (lEnd s i) = idD s i := by
  rcases lEnd_spec s i with ⟨he, _⟩ | ⟨_, hs⟩
  · rw [he]
  · have h := hs.2.2
    rw [idAt_eq_idD hi, idAt_eq_idD (lEnd_lt hi)] at h
    exact (Option.some.inj h).symm

private theorem idD_mem {s : List (ℕ × Letter I)} {i : ℕ} (hi : i < s.length) :
    idD s i ∈ s.map Prod.fst := by
  refine List.mem_map.mpr ⟨s[i], List.getElem_mem hi, ?_⟩
  simp [idD, idAt, List.getElem?_eq_getElem hi]

/-- Left-endpoint strand names are in bijection with the IDs actually present
in a valid matching. This avoids assuming a cyclic cut preserves left endpoints. -/
noncomputable def strandIdEquiv (a : List (Letter I)) (R : List (TMove (Letter I)))
    (hv : Valid (pairing₂ a R)) :
    MatchingStrand a R ≃ {n : ℕ // n ∈ (pairing₂ a R).map Prod.fst} := by
  let f : MatchingStrand a R → {n : ℕ // n ∈ (pairing₂ a R).map Prod.fst} :=
    fun j => ⟨idD (pairing₂ a R) j.val, idD_mem (mem_leftEnds₂.mp j.property).1⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    have hid := congrArg Subtype.val hij
    have h := lEnd_eq_of_idD hv (Iso.refl _) (mem_leftEnds₂.mp i.property).1
      (mem_leftEnds₂.mp j.property) hid
    have hi := lEnd_eq_of_isLeftEnd hv (mem_leftEnds₂.mp i.property) (Or.inl rfl)
    exact Subtype.ext (hi.symm.trans h)
  · intro n
    obtain ⟨z, hz, he⟩ := List.mem_map.mp n.property
    obtain ⟨i, hi, hiZ⟩ := List.mem_iff_getElem.mp hz
    refine ⟨⟨lEnd (pairing₂ a R) i, mem_leftEnds₂.mpr (isLeftEnd_lEnd hv hi)⟩, ?_⟩
    apply Subtype.ext
    change idD (pairing₂ a R) (lEnd (pairing₂ a R) i) = n.val
    rw [idD_lEnd hi]
    simpa only [idD, idAt, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some,
      hiZ] using he

@[simp] theorem strandIdEquiv_val (a : List (Letter I)) (R : List (TMove (Letter I)))
    (hv : Valid (pairing₂ a R)) (j : MatchingStrand a R) :
    (strandIdEquiv a R hv j).val = idD (pairing₂ a R) j.val := rfl

theorem attach_ids_perm {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R) :
    ((pairing₂ (a ++ [x]) (attach b R)).map Prod.fst).Perm
      (((pairing₂ a R).map Prod.fst).map (fun n => n + 2)) := by
  obtain ⟨_, P, q, hs, hp, _⟩ := attach_matching_state hR
  rw [hs, hp]
  simp only [List.map_cons, List.map_append, List.map_nil, List.map_map, liftId,
    Function.comp_def]
  exact List.perm_append_comm (l₁ := [q + 2]) (l₂ := P.map fun z => z.1 + 2)

noncomputable def attachIdEquiv {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R) :
    {n : ℕ // n ∈ (pairing₂ a R).map Prod.fst} ≃
      {n : ℕ // n ∈ (pairing₂ (a ++ [x]) (attach b R)).map Prod.fst} := by
  let f : {n : ℕ // n ∈ (pairing₂ a R).map Prod.fst} →
      {n : ℕ // n ∈ (pairing₂ (a ++ [x]) (attach b R)).map Prod.fst} := fun n =>
    ⟨n.val + 2, (attach_ids_perm hR).mem_iff.mpr (List.mem_map.mpr ⟨n.val, n.property, rfl⟩)⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    exact Subtype.ext (Nat.add_right_cancel (congrArg Subtype.val hij))
  · intro n
    obtain ⟨m, hm, he⟩ := List.mem_map.mp ((attach_ids_perm hR).mem_iff.mp n.property)
    exact ⟨⟨m, hm⟩, Subtype.ext he⟩

/-- Actual strand transport across the cyclic boundary cut. The left endpoint
may change, so transport is through the injectively shifted strand IDs. -/
noncomputable def attachStrandEquiv {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R) :
    MatchingStrand a R ≃ MatchingStrand (a ++ [x]) (attach b R) :=
  (strandIdEquiv a R hR.pairing_properties.1).trans
    ((attachIdEquiv hR).trans
      (strandIdEquiv (a ++ [x]) (attach b R) (attach_matching hR).pairing_properties.1).symm)

/-- Strand transport preserves the exact shifted ID, including the strand
whose endpoint passes through the cyclic cut. -/
theorem attachStrandEquiv_id {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R)
    (j : MatchingStrand a R) :
    idD (pairing₂ (a ++ [x]) (attach b R)) (attachStrandEquiv hR j).val =
      idD (pairing₂ a R) j.val + 2 := by
  have h := congrArg Subtype.val
    ((strandIdEquiv (a ++ [x]) (attach b R) (attach_matching hR).pairing_properties.1).apply_symm_apply
      (attachIdEquiv hR (strandIdEquiv a R hR.pairing_properties.1 j)))
  exact h

private theorem frame_cap_ren (x : Letter I) (T : TState (Letter I))
    (P : List (ℕ × Letter I)) (q n : ℕ) (hs : T.st = P ++ [(q, flipL x)]) :
    stepRen 0 (frame x T) (.cap (P.length + 1)) (n + 2) = n + 2 := by
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
  simp only [stepRen, Nat.zero_add, idD, idAt, hA, hB, Option.map_some, Option.getD_some]
  simp [rlId]

/-- The final cap changes only the outer ID 0, never any old strand ID. -/
theorem frame_ren_append_cap (x : Letter I) (k : ℕ) (T : TState (Letter I))
    (R : List (TMove (Letter I))) (hR : TFits flipL k T R)
    (P : List (ℕ × Letter I)) (q : ℕ)
    (hs : (tRun flipL k T R).st = P ++ [(q, flipL x)])
    (g : ℕ) (hg : k + g = P.length) (n : ℕ) :
    tRen (k + 1) (frame x T) (R ++ [.cap g]) (n + 2) = tRen k T R n + 2 := by
  rw [tRen_append_at, frame_ren x k T R hR n, (frame_run x k T R hR).2]
  change stepRen (k + 1) (frame x (tRun flipL k T R)) (.cap g) (_ + 2) = _
  have h := frame_cap_ren x (tRun flipL k T R) P q (tRen k T R n) hs
  simpa only [stepRen, Nat.zero_add, show k + 1 + g = P.length + 1 by omega] using h

/-- A bounded distinguished point stays at the same height and position on
the corresponding strand after the right cap. -/
theorem onStrand_attach {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R)
    (j : MatchingStrand a R) {p : ℕ × ℕ} (hbound : p.1 ≤ R.length)
    (hp : OnStrand₂ a R j.val p) :
    p.1 ≤ (attach b R).length ∧
      OnStrand₂ (a ++ [x]) (attach b R) (attachStrandEquiv hR j).val p := by
  let T := tRun flipL a.length (tStart a) (R.take p.1)
  have hsplit := (tFits_append_at a.length (tStart a) (R.take p.1) (R.drop p.1)).mp
    (by simpa only [List.take_append_drop] using hR.1)
  have hrun := (frame_run x a.length (tStart a) (R.take p.1) hsplit.1).2
  have htake : (attach b R).take p.1 = R.take p.1 := List.take_append_of_le_length hbound
  have hdrop : (attach b R).drop p.1 = R.drop p.1 ++ [.cap b.length] :=
    List.drop_append_of_le_length hbound
  have hnew : tRun flipL (a ++ [x]).length (tStart (a ++ [x])) ((attach b R).take p.1) =
      frame x T := by
    rw [htake]
    simpa only [List.length_append, List.length_singleton, frame_start] using hrun
  have hfold := (dLay_right (length_dualW a) [x] ((R.take p.1).map .tm)
    (tStart a) a (tStart_letters a) (by simpa only [tmoves_map_tm] using hsplit.1)
    (dOk₂_map_tm a (R.take p.1))).2
  simp only [tmoves_map_tm] at hfold
  have hlet := letters_tRun (length_dualW a) (R.take p.1) (tStart a) a
    (tStart_letters a) hsplit.1
  have hlen : T.st.length = a.length + ((R.take p.1).foldl tLet a).length := by
    have hh := congrArg List.length hlet
    simpa only [List.length_map, List.length_append, length_dualW] using hh
  obtain ⟨_, P, q, hs, _, _⟩ := attach_matching_state hR
  have hPlen : a.length + b.length = P.length := by
    have h₁ := congrArg List.length hs
    have h₂ := congrArg List.length hR.pairing_properties.2.2
    simp only [List.length_map, List.length_append, length_dualW, List.length_singleton] at h₁ h₂
    omega
  have htail : tRun flipL a.length T (R.drop p.1) = tRun flipL a.length (tStart a) R := by
    simp only [T, tRun, ← List.foldl_append, List.take_append_drop]
  have hren := frame_ren_append_cap x a.length T (R.drop p.1) hsplit.2 P q
    (by rw [htail]; exact hs) b.length hPlen (idD T.st (a.length + p.2))
  refine ⟨by simp only [attach, List.length_append, List.length_singleton]; omega, ?_, ?_⟩
  · rw [htake, hfold, List.length_append, List.length_singleton]
    exact Nat.lt_succ_of_lt hp.1
  ·

    rw [hnew, hdrop, show (a ++ [x]).length = a.length + 1 by simp,
      show a.length + 1 + p.2 = (a.length + p.2) + 1 by omega,
      idD_frame x T (by have := hp.1; omega), hren, attachStrandEquiv_id hR j]
    exact congrArg (fun n => n + 2) hp.2

noncomputable def attachPoints {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R)
    (q : ℕ → ℕ × ℕ) (j : ℕ) : ℕ × ℕ := by
  classical
  exact if h : j ∈ leftEnds₂ (a ++ [x]) (attach b R) then
    q ((attachStrandEquiv hR).symm ⟨j, h⟩).val else (0, 0)

@[simp] theorem attachPoints_apply {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R)
    (q : ℕ → ℕ × ℕ) (j : MatchingStrand (a ++ [x]) (attach b R)) :
    attachPoints hR q j.val = q ((attachStrandEquiv hR).symm j).val := by
  simp only [attachPoints, dite_eq_left j.property]

private theorem dotList_attach (a : List (Letter I)) (R : List (TMove (Letter I)))
    (q : ℕ → ℕ × ℕ) (n : MatchingStrand a R → ℕ) :
    (leftEnds₂ a R).flatMap (fun j => List.replicate (strandCounts n j) (q j)) =
      (leftEnds₂ a R).attach.flatMap (fun j => List.replicate (n j) (q j.val)) := by
  conv_lhs => rw [← List.attach_map_subtype_val (leftEnds₂ a R), List.flatMap_map]
  congr 1
  funext j
  simp only [strandCounts_apply]

/-- Literal cap attachment transports every strand multiplicity, including
arbitrary repeated dots and serializers, across the cyclic boundary cut. -/
theorem attach_decorates {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R)
    (q : ℕ → ℕ × ℕ) (n : MatchingStrand a R → ℕ) {ds : List (DTMove I)}
    (hd : Decorates₂ a R q (strandCounts n) ds) :
    Decorates₂ (a ++ [x]) (attach b R) (attachPoints hR q)
      (strandCounts (n ∘ (attachStrandEquiv hR).symm)) (attachMoves b ds) := by
  classical
  refine ⟨by rw [tmoves_attachMoves, hd.1], ?_⟩
  rw [dotPts_attachMoves]
  apply hd.2.trans
  rw [dotList_attach, dotList_attach]
  have he : ((leftEnds₂ (a ++ [x]) (attach b R)).attach.map (attachStrandEquiv hR).symm).Perm
      (leftEnds₂ a R).attach := by
    apply (List.perm_ext_iff_of_nodup
      ((nodup_leftEnds₂ _ _).attach.map (attachStrandEquiv hR).symm.injective)
      (nodup_leftEnds₂ _ _).attach).mpr
    intro j
    simp only [List.mem_attach, iff_true, List.mem_map]
    exact ⟨attachStrandEquiv hR j, trivial, (attachStrandEquiv hR).symm_apply_apply j⟩
  have hp := he.symm.flatMap_right (fun j : MatchingStrand a R => List.replicate (n j) (q j.val))
  simpa only [List.flatMap_map, Function.comp_apply, attachPoints_apply] using hp

/-- Transported distinguished points remain bounded and on their actual strands. -/
theorem attachPoints_spec {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R)
    (q : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ a R, (q j).1 ≤ R.length ∧ OnStrand₂ a R j (q j))
    (j : MatchingStrand (a ++ [x]) (attach b R)) :
    (attachPoints hR q j.val).1 ≤ (attach b R).length ∧
      OnStrand₂ (a ++ [x]) (attach b R) j.val (attachPoints hR q j.val) := by
  rw [attachPoints_apply]
  have h := onStrand_attach hR ((attachStrandEquiv hR).symm j)
    (hq _ ((attachStrandEquiv hR).symm j).property).1
    (hq _ ((attachStrandEquiv hR).symm j).property).2
  simpa only [Equiv.apply_symm_apply] using h

/-- Bend an entire target suffix down, starting at its rightmost endpoint. -/
def suffixMatching (b : List (Letter I)) : List (Letter I) →
    List (TMove (Letter I)) → List (TMove (Letter I))
  | [], R => R
  | y :: w, R => attach b (suffixMatching (b ++ [y]) w R)

def suffixMoves (b : List (Letter I)) : List (Letter I) →
    List (DTMove I) → List (DTMove I)
  | [], ds => ds
  | y :: w, ds => attachMoves b (suffixMoves (b ++ [y]) w ds)

@[simp] theorem tmoves_suffixMoves (b w : List (Letter I)) (ds : List (DTMove I)) :
    tmoves (suffixMoves b w ds) = suffixMatching b w (tmoves ds) := by
  induction w generalizing b with
  | nil => rfl
  | cons y w ih => simp only [suffixMoves, suffixMatching, tmoves_attachMoves, ih]

@[simp] theorem dotPts_suffixMoves (b w : List (Letter I)) (ds : List (DTMove I)) :
    dotPts (suffixMoves b w ds) = dotPts ds := by
  induction w generalizing b with
  | nil => rfl
  | cons y w ih => simp only [suffixMoves, dotPts_attachMoves, ih]

/-- Iterated literal inverse mates are genuine matchings. -/
theorem suffix_matching {a b w : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (b ++ w) R) :
    IsMatching₂ (a ++ dualW w) b (suffixMatching b w R) := by
  induction w generalizing a b R with
  | nil => simpa only [suffixMatching, dualW_nil, List.append_nil] using hR
  | cons y w ih =>
    have hR' : IsMatching₂ a ((b ++ [y]) ++ w) R := by simpa using hR
    have hm := ih hR'
    have hm' : IsMatching₂ (a ++ dualW w) (b ++ [flipL (flipL y)])
        (suffixMatching (b ++ [y]) w R) := by simpa only [flipL_involutive y] using hm
    have h := attach_matching hm'
    simpa only [suffixMatching, dualW_cons, List.append_assoc] using h

/-- Weak reducedness is preserved throughout the entire target-suffix bend. -/
theorem suffix_reduced {a b w : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (b ++ w) R) (hred : Reduced₂ a R) :
    Reduced₂ (a ++ dualW w) (suffixMatching b w R) := by
  induction w generalizing a b R with
  | nil => simpa only [suffixMatching, dualW_nil, List.append_nil] using hred
  | cons y w ih =>
    have hR' : IsMatching₂ a ((b ++ [y]) ++ w) R := by simpa using hR
    have hm : IsMatching₂ (a ++ dualW w) (b ++ [flipL (flipL y)])
        (suffixMatching (b ++ [y]) w R) := by
      simpa only [flipL_involutive y] using suffix_matching hR'
    have h := attach_reduced hm (ih hR' hred)
    simpa only [suffixMatching, dualW_cons, List.append_assoc] using h

@[simp] theorem ncr_suffixMatching (b w : List (Letter I)) (R : List (TMove (Letter I))) :
    ncr₂ (suffixMatching b w R) = ncr₂ R := by
  induction w generalizing b with
  | nil => rfl
  | cons y w ih => simp only [suffixMatching, ncr_attach, ih]

/-- The entire suffix bend has a strand bijection preserving every bounded
actual point. In particular, strands passing through successive cyclic cuts
retain their dot multiplicities. -/
theorem exists_suffixStrandEquiv {a b w : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (b ++ w) R) :
    ∃ e : MatchingStrand a R ≃ MatchingStrand (a ++ dualW w) (suffixMatching b w R),
      ∀ (j : MatchingStrand a R) (p : ℕ × ℕ), p.1 ≤ R.length → OnStrand₂ a R j.val p →
        p.1 ≤ (suffixMatching b w R).length ∧
          OnStrand₂ (a ++ dualW w) (suffixMatching b w R) (e j).val p := by
  induction w generalizing a b R with
  | nil =>
    rw [dualW_nil, List.append_nil]
    simpa only [suffixMatching] using
      (show ∃ e : MatchingStrand a R ≃ MatchingStrand a R,
        ∀ (j : MatchingStrand a R) (p : ℕ × ℕ), p.1 ≤ R.length → OnStrand₂ a R j.val p →
          p.1 ≤ R.length ∧ OnStrand₂ a R (e j).val p from
        ⟨Equiv.refl _, fun _ _ hb hp => ⟨hb, hp⟩⟩)
  | cons y w ih =>
    have hR' : IsMatching₂ a ((b ++ [y]) ++ w) R := by simpa using hR
    obtain ⟨e, he⟩ := ih hR'
    have hm : IsMatching₂ (a ++ dualW w) (b ++ [flipL (flipL y)])
        (suffixMatching (b ++ [y]) w R) := by
      simpa only [flipL_involutive y] using suffix_matching hR'
    have h : ∃ E : MatchingStrand a R ≃
        MatchingStrand ((a ++ dualW w) ++ [flipL y]) (attach b (suffixMatching (b ++ [y]) w R)),
        ∀ (j : MatchingStrand a R) (p : ℕ × ℕ), p.1 ≤ R.length → OnStrand₂ a R j.val p →
          p.1 ≤ (attach b (suffixMatching (b ++ [y]) w R)).length ∧
            OnStrand₂ ((a ++ dualW w) ++ [flipL y]) (attach b (suffixMatching (b ++ [y]) w R))
              (E j).val p := by
      refine ⟨e.trans (attachStrandEquiv hm), ?_⟩
      intro j p hb hp
      exact onStrand_attach hm (e j) (he j p hb hp).1 (he j p hb hp).2
    rw [dualW_cons, ← List.append_assoc]
    exact h

noncomputable def suffixStrandEquiv {a b w : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (b ++ w) R) :
    MatchingStrand a R ≃ MatchingStrand (a ++ dualW w) (suffixMatching b w R) :=
  (exists_suffixStrandEquiv hR).choose

theorem onStrand_suffix {a b w : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (b ++ w) R) (j : MatchingStrand a R) (p : ℕ × ℕ)
    (hb : p.1 ≤ R.length) (hp : OnStrand₂ a R j.val p) :
    p.1 ≤ (suffixMatching b w R).length ∧
      OnStrand₂ (a ++ dualW w) (suffixMatching b w R) (suffixStrandEquiv hR j).val p :=
  (exists_suffixStrandEquiv hR).choose_spec j p hb hp

noncomputable def suffixPoints {a b w : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (b ++ w) R) (q : ℕ → ℕ × ℕ) (j : ℕ) : ℕ × ℕ := by
  classical
  exact if h : j ∈ leftEnds₂ (a ++ dualW w) (suffixMatching b w R) then
    q ((suffixStrandEquiv hR).symm ⟨j, h⟩).val else (0, 0)

@[simp] theorem suffixPoints_apply {a b w : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (b ++ w) R) (q : ℕ → ℕ × ℕ)
    (j : MatchingStrand (a ++ dualW w) (suffixMatching b w R)) :
    suffixPoints hR q j.val = q ((suffixStrandEquiv hR).symm j).val := by
  simp only [suffixPoints, dite_eq_left j.property]

theorem suffix_decorates {a b w : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (b ++ w) R) (q : ℕ → ℕ × ℕ) (n : MatchingStrand a R → ℕ)
    {ds : List (DTMove I)} (hd : Decorates₂ a R q (strandCounts n) ds) :
    Decorates₂ (a ++ dualW w) (suffixMatching b w R) (suffixPoints hR q)
      (strandCounts (n ∘ (suffixStrandEquiv hR).symm)) (suffixMoves b w ds) := by
  classical
  refine ⟨by rw [tmoves_suffixMoves, hd.1], ?_⟩
  rw [dotPts_suffixMoves]
  apply hd.2.trans
  rw [dotList_attach, dotList_attach]
  have he : ((leftEnds₂ (a ++ dualW w) (suffixMatching b w R)).attach.map
      (suffixStrandEquiv hR).symm).Perm (leftEnds₂ a R).attach := by
    apply (List.perm_ext_iff_of_nodup
      ((nodup_leftEnds₂ _ _).attach.map (suffixStrandEquiv hR).symm.injective)
      (nodup_leftEnds₂ _ _).attach).mpr
    intro j
    simp only [List.mem_attach, iff_true, List.mem_map]
    exact ⟨suffixStrandEquiv hR j, trivial, (suffixStrandEquiv hR).symm_apply_apply j⟩
  have hp := he.symm.flatMap_right (fun j : MatchingStrand a R => List.replicate (n j) (q j.val))
  simpa only [List.flatMap_map, Function.comp_apply, suffixPoints_apply] using hp

theorem suffixPoints_spec {a b w : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (b ++ w) R) (q : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ a R, (q j).1 ≤ R.length ∧ OnStrand₂ a R j (q j))
    (j : MatchingStrand (a ++ dualW w) (suffixMatching b w R)) :
    (suffixPoints hR q j.val).1 ≤ (suffixMatching b w R).length ∧
      OnStrand₂ (a ++ dualW w) (suffixMatching b w R) j.val (suffixPoints hR q j.val) := by
  rw [suffixPoints_apply]
  have h := onStrand_suffix hR ((suffixStrandEquiv hR).symm j) _
    (hq _ ((suffixStrandEquiv hR).symm j).property).1
    (hq _ ((suffixStrandEquiv hR).symm j).property).2
  simpa only [Equiv.apply_symm_apply] using h

private theorem dOk_right {k : ℕ} {u : List (Letter I)} (hu : u.length = k)
    (v : List (Letter I)) (ds : List (DTMove I)) (T : TState (Letter I))
    (l : List (Letter I)) (hl : T.st.map Prod.snd = u ++ l)
    (hf : TFits flipL k T (tmoves ds)) (hd : DOk₂ l ds) : DOk₂ (l ++ v) ds := by
  induction ds generalizing T l with
  | nil => trivial
  | cons d ds ih =>
    cases d with
    | tm m =>
      have hm := lOk_at hu hl hf.1
      have hn := letters_tRun hu [m] T l hl ⟨hf.1, trivial⟩
      simp only [tRun, List.foldl_cons, List.foldl_nil] at hn
      change DOk₂ (tLet (l ++ v) m) ds
      rw [(tmLay_right v hm).2]
      exact ih _ _ hn hf.2 hd
    | dt p =>
      refine ⟨?_, ih _ _ hl hf hd.2⟩
      have h := hd.1
      simp only [List.length_append]
      omega

theorem dOk_attachMoves {x : Letter I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (b ++ [flipL x]) R)
    {ds : List (DTMove I)} (hm : tmoves ds = R) (hd : DOk₂ a ds) :
    DOk₂ (a ++ [x]) (attachMoves b ds) := by
  apply (dOk₂_append _ _ _).mpr
  exact ⟨dOk_right (length_dualW a) [x] ds (tStart a) a (tStart_letters a)
    (by rw [hm]; exact hR.1) hd, trivial⟩

theorem dOk_suffixMoves {a b w : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (b ++ w) R) {ds : List (DTMove I)}
    (hm : tmoves ds = R) (hd : DOk₂ a ds) :
    DOk₂ (a ++ dualW w) (suffixMoves b w ds) := by
  induction w generalizing a b R ds with
  | nil => simpa only [suffixMoves, dualW_nil, List.append_nil] using hd
  | cons y w ih =>
    have hR' : IsMatching₂ a ((b ++ [y]) ++ w) R := by simpa using hR
    have hmatch : IsMatching₂ (a ++ dualW w) (b ++ [flipL (flipL y)])
        (suffixMatching (b ++ [y]) w R) := by
      simpa only [flipL_involutive y] using suffix_matching hR'
    have h := dOk_attachMoves hmatch (by rw [tmoves_suffixMoves, hm]) (ih hR' hm hd)
    simpa only [suffixMoves, dualW_cons, List.append_assoc] using h

/-- Literal layers for iterated right-target cap attachment. -/
def suffixLayers (b : List (Letter I)) : List (Letter I) → List (XLayer I) → List (XLayer I)
  | [], L => L
  | y :: w, L => (suffixLayers (b ++ [y]) w L).map (xwhL [] [flipL y]) ++
      (xCapL (flipL y)).map (xwhL b [])

theorem dLay_suffixMoves {a b w : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (b ++ w) R) {ds : List (DTMove I)}
    (hm : tmoves ds = R) (hd : DOk₂ a ds) :
    dLay (a ++ dualW w) (suffixMoves b w ds) = suffixLayers b w (dLay a ds) := by
  induction w generalizing a b R ds with
  | nil => simp only [suffixMoves, suffixLayers, dualW_nil, List.append_nil]
  | cons y w ih =>
    have hR' : IsMatching₂ a ((b ++ [y]) ++ w) R := by simpa using hR
    have hmatch : IsMatching₂ (a ++ dualW w) (b ++ [flipL (flipL y)])
        (suffixMatching (b ++ [y]) w R) := by
      simpa only [flipL_involutive y] using suffix_matching hR'
    have h := dLay_attachMoves hmatch (by rw [tmoves_suffixMoves, hm]) (dOk_suffixMoves hR' hm hd)
    rw [ih hR' hm hd] at h
    simpa only [suffixMoves, suffixLayers, dualW_cons, List.append_assoc] using h

end OddMath.SKM.RightCapAttachment
