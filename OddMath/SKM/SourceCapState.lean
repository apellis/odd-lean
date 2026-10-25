import OddMath.SKM.SourceIdRelabel

/-! # Initial source caps

State identities for the isolated source cap in the contextual sorting step
of [BE2, Section 8]. The cap consumes the active endpoints in source order;
its surviving ID is that of the left active endpoint, hence the *right*
frozen endpoint. The layer orientation is read from `tmLay`, not imposed.
-/
namespace OddMath.SKM.SourceCapState
open StringDiagrams StringDiagrams.Chord
variable {I : Type*}

/-- Nested-cup IDs with an initial offset. -/
def indexed (n : ℕ) (w : List (Letter I)) : List (ℕ × Letter I) :=
  w.mapIdx fun j x => (n + 2 * j, x)

@[simp] theorem indexed_length (n : ℕ) (w : List (Letter I)) :
    (indexed n w).length = w.length := by simp [indexed]

 theorem indexed_append (n : ℕ) (v w : List (Letter I)) :
    indexed n (v ++ w) = indexed n v ++ indexed (n + 2 * v.length) w := by
  simp only [indexed, List.mapIdx_append]
  congr 1
  simp only [List.mapIdx_eq_zipIdx_map]
  apply List.map_congr_left
  intro z _
  congr 1; omega

 theorem indexed_cons (n : ℕ) (x : Letter I) (w : List (Letter I)) :
    indexed n (x :: w) = (n, x) :: indexed (n + 2) w := by
  simp only [indexed, List.mapIdx_cons, Nat.mul_zero, Nat.add_zero]
  congr 1
  simp only [List.mapIdx_eq_zipIdx_map]
  apply List.map_congr_left
  intro z _
  congr 1; omega

/-- The frozen portion before the selected pair. -/
def before (Q : List (Letter I)) := indexed 0 (dualW Q)
/-- The frozen portion after the selected pair. -/
def after (L Q : List (Letter I)) := indexed (2 * Q.length + 4) (dualW L)

/-- Exact nested-cup decomposition at a contextual opposite pair. -/
theorem start_st (L Q : List (Letter I)) (x : Letter I) :
    (tStart (L ++ flipL x :: x :: Q)).st =
      (before Q ++ (2 * Q.length, flipL x) :: (2 * Q.length + 2, x) :: after L Q) ++
      (after L Q).reverse.map flipSnd ++
      (2 * Q.length + 2, flipL x) :: (2 * Q.length, x) ::
        (before Q).reverse.map flipSnd := by
  have he : cupLeft (dualW (L ++ flipL x :: x :: Q)) =
      before Q ++ (2 * Q.length, flipL x) :: (2 * Q.length + 2, x) :: after L Q := by
    rw [show cupLeft (dualW (L ++ flipL x :: x :: Q)) =
      indexed 0 (dualW (L ++ flipL x :: x :: Q)) by simp [cupLeft, indexed]]
    simp only [dualW_append, dualW_cons, flipL_flipL]
    rw [indexed_append, indexed_append]
    simp [indexed, before, after, length_dualW, Nat.mul_add, Nat.add_assoc]
  simp only [tStart, run_cupMoves, he, List.reverse_append, List.reverse_cons,
    List.map_append, List.map_cons, List.map_nil]
  simp [flipSnd, flipL_flipL, List.append_assoc]

/-- Initial cap state: its two remaining endpoints are frozen, with the ID
of the left active leg. All residual active endpoints retain their IDs. -/
def capped (L Q : List (Letter I)) (x : Letter I) : TState (Letter I) :=
  ⟨2 * (L.length + Q.length + 2),
    ((before Q ++ (2 * Q.length, flipL x) :: (2 * Q.length + 2, x) :: after L Q) ++
      (after L Q).reverse.map flipSnd ++ (before Q).reverse.map flipSnd).map
        (rl (2 * Q.length) (2 * Q.length + 2)), []⟩

 theorem start_cap (L Q : List (Letter I)) (x : Letter I) :
    tStep flipL (L ++ flipL x :: x :: Q).length
      (tStart (L ++ flipL x :: x :: Q)) (.cap L.length) = capped L Q x := by
  have hlen : (L ++ flipL x :: x :: Q).length + L.length =
      ((before Q ++ (2 * Q.length, flipL x) :: (2 * Q.length + 2, x) :: after L Q) ++
        (after L Q).reverse.map flipSnd).length := by
    simp [before, after, length_dualW]; omega
  simp only [tStep, start_st]
  rw [show (before Q ++ (2 * Q.length, flipL x) :: (2 * Q.length + 2, x) :: after L Q) ++
      (after L Q).reverse.map flipSnd ++
      (2 * Q.length + 2, flipL x) :: (2 * Q.length, x) :: (before Q).reverse.map flipSnd =
    ((before Q ++ (2 * Q.length, flipL x) :: (2 * Q.length + 2, x) :: after L Q) ++
      (after L Q).reverse.map flipSnd) ++
      (2 * Q.length + 2, flipL x) :: (2 * Q.length, x) :: (before Q).reverse.map flipSnd by
        simp [List.append_assoc]]
  rw [hlen]
  rw [show ∀ (P W : List (ℕ × Letter I)) (A B : ℕ × Letter I),
      jn (P ++ A :: B :: W) P.length = (P ++ W).map (rl B.1 A.1) by
        intro P W A B
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using jn_mid P W A B]
  simp only [capped, tStart, run_cupMoves, List.length_append, List.length_map,
    List.length_reverse, length_cupLeft, length_dualW, List.length_cons, List.map_nil]
  congr 1; omega

/-- The two cap inputs have different IDs and dual letters. -/
theorem cap_ok (L Q : List (Letter I)) (x : Letter I) :
    (TMove.cap L.length).Ok flipL (L ++ flipL x :: x :: Q).length
      (tStart (L ++ flipL x :: x :: Q)).st := by
  rw [start_st]
  refine ⟨(2 * Q.length + 2, flipL x), (2 * Q.length, x), ?_, ?_, rfl, by omega⟩
  all_goals
    have hlen : (L ++ flipL x :: x :: Q).length + L.length =
        ((before Q ++ (2 * Q.length, flipL x) :: (2 * Q.length + 2, x) :: after L Q) ++
          (after L Q).reverse.map flipSnd).length := by
      simp [before, after, length_dualW]; omega
    rw [hlen]
    simp only [List.getElem?_append, List.length_append, List.length_cons,
      List.length_map, List.length_reverse] at *
    split_ifs <;> simp_all

/-- The cap layer is `xCapL x`: upward second endpoint gives `lcap`,
downward second endpoint gives the presentation cap. -/
theorem cap_layers (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) :
    tLay (L ++ flipL x :: x :: Q) (.cap L.length :: R) =
      (xCapL x).map (xwhL L Q) ++ tLay (L ++ Q) R := by
  simp only [tLay, (tmLay_cap L Q (flipL x) x).1, (tmLay_cap L Q (flipL x) x).2]

/-- The two actual active strand IDs; the frozen order is reversed. -/
theorem cap_ids (L Q : List (Letter I)) (x : Letter I) :
    idD (tStart (L ++ flipL x :: x :: Q)).st
        ((L ++ flipL x :: x :: Q).length + L.length) = 2 * Q.length + 2 ∧
    idD (tStart (L ++ flipL x :: x :: Q)).st
        ((L ++ flipL x :: x :: Q).length + L.length + 1) = 2 * Q.length := by
  rw [start_st]
  have hlen : (L ++ flipL x :: x :: Q).length + L.length =
      ((before Q ++ (2 * Q.length, flipL x) :: (2 * Q.length + 2, x) :: after L Q) ++
        (after L Q).reverse.map flipSnd).length := by
    simp [before, after, length_dualW]; omega
  rw [hlen]
  simp only [idD, idAt, List.getElem?_append, List.length_append, List.length_cons,
    List.length_map, List.length_reverse]
  split_ifs <;> simp_all

/-- The initial cap renames the right active ID to the left active ID. -/
theorem cap_ren (L Q : List (Letter I)) (x : Letter I) :
    stepRen (L ++ flipL x :: x :: Q).length (tStart (L ++ flipL x :: x :: Q))
      (.cap L.length) = rlId (2 * Q.length) (2 * Q.length + 2) := by
  simp only [stepRen, (cap_ids L Q x).1, (cap_ids L Q x).2]

/-- One critical point is created, on the surviving cap ID. -/
theorem cap_crit (L Q : List (Letter I)) (x : Letter I) (cl : List ℕ) :
    critStep (L ++ flipL x :: x :: Q).length (tStart (L ++ flipL x :: x :: Q))
      cl (.cap L.length) = cl.map (rlId (2 * Q.length) (2 * Q.length + 2)) ++
        [2 * Q.length + 2] := by
  simp only [critStep, (cap_ids L Q x).1, (cap_ids L Q x).2]

/-- All remaining validity obligations start at the explicit capped state. -/
theorem fits_cap (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) :
    TFits flipL (L ++ flipL x :: x :: Q).length (tStart (L ++ flipL x :: x :: Q))
      (.cap L.length :: R) ↔
    TFits flipL (L ++ flipL x :: x :: Q).length (capped L Q x) R := by
  simp only [TFits, cap_ok L Q x, start_cap, true_and]

/-- The complete run, including all later ID renamings and crossings. -/
theorem run_cap (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) :
    tRun flipL (L ++ flipL x :: x :: Q).length (tStart (L ++ flipL x :: x :: Q))
      (.cap L.length :: R) =
    tRun flipL (L ++ flipL x :: x :: Q).length (capped L Q x) R := by
  change tRun flipL _ (tStep flipL _ _ _) R = _
  rw [start_cap]

/-- Exact distinguished-point transport through an initial cap and suffix. -/
theorem ren_cap (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) (z : ℕ) :
    tRen (L ++ flipL x :: x :: Q).length (tStart (L ++ flipL x :: x :: Q))
      (.cap L.length :: R) z =
    tRen (L ++ flipL x :: x :: Q).length (capped L Q x) R
      (rlId (2 * Q.length) (2 * Q.length + 2) z) := by
  simp only [tRen, start_cap, cap_ren]

/-- Exact critical-ID list for the complete initial-cap matching. -/
theorem crit_cap (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) :
    tCrit flipL (L ++ flipL x :: x :: Q).length (tStart (L ++ flipL x :: x :: Q))
      [] (.cap L.length :: R) =
    tCrit flipL (L ++ flipL x :: x :: Q).length (capped L Q x)
      [2 * Q.length + 2] R := by
  simp only [tCrit, start_cap, cap_crit, List.map_nil, List.nil_append]

/-- The corresponding residual nested-cup state. Comparing with `start_st`
shows precisely where the two deleted source endpoints shift old IDs by four.
In particular, the fresh counter is four smaller, not two smaller. -/
theorem residual_start (L Q : List (Letter I)) :
    tStart (L ++ Q) =
      ⟨2 * (L.length + Q.length),
        (before Q ++ indexed (2 * Q.length) (dualW L)) ++
        (indexed (2 * Q.length) (dualW L)).reverse.map flipSnd ++
        (before Q).reverse.map flipSnd, []⟩ := by
  have he : cupLeft (dualW (L ++ Q)) = before Q ++ indexed (2 * Q.length) (dualW L) := by
    rw [show cupLeft (dualW (L ++ Q)) = indexed 0 (dualW (L ++ Q)) by
      simp [cupLeft, indexed], dualW_append, indexed_append]
    simp [before, length_dualW]
  simp only [tStart, run_cupMoves, he, List.length_append, List.length_map,
    List.length_reverse, indexed_length, List.reverse_append, List.map_append]
  simp only [before, indexed_length, length_dualW, List.append_assoc]
  congr 1
  omega

/-- Both frozen endpoints of the isolated cap carry the surviving ID. -/
theorem frozen_cap_ids (L Q : List (Letter I)) (x : Letter I) :
    idAt (capped L Q x).st Q.length = some (2 * Q.length + 2) ∧
    idAt (capped L Q x).st (Q.length + 1) = some (2 * Q.length + 2) := by
  have hl : (before Q).length = Q.length := by simp [before, length_dualW]
  simp only [capped, List.map_append, List.map_cons, idAt, List.getElem?_append,
    List.length_map, List.length_append, List.length_cons, hl]
  have h0 : Q.length < Q.length + ((after L Q).length + 1 + 1) + (after L Q).length := by omega
  have h1 : Q.length + 1 < Q.length + ((after L Q).length + 1 + 1) + (after L Q).length := by omega
  simp [rl, rlId, h0, h1]

/-- A lone contextual initial cap is a valid matching to the residual word. -/
theorem cap_matching (L Q : List (Letter I)) (x : Letter I) :
    IsMatching₂ (L ++ flipL x :: x :: Q) (L ++ Q) [.cap L.length] := by
  refine ⟨⟨cap_ok L Q x, trivial⟩, ?_⟩
  exact (tmLay_cap L Q (flipL x) x).2

/-- The isolated cap has no crossings and exactly one critical point. -/
theorem cap_strict (L Q : List (Letter I)) (x : Letter I) :
    StrictReduced₂ (L ++ flipL x :: x :: Q) [.cap L.length] := by
  unfold StrictReduced₂ Reduced₂ critPts₂
  rw [run_cap, crit_cap]
  simp [tRun, tCrit, capped]

/-- Strictness after attachment is an exact condition on the complete capped
run, including the initial cap in the critical-ID list. -/
theorem strict_cap_iff (L Q : List (Letter I)) (x : Letter I)
    (R : List (TMove (Letter I))) :
    StrictReduced₂ (L ++ flipL x :: x :: Q) (.cap L.length :: R) ↔
      ((tRun flipL (L ++ flipL x :: x :: Q).length (capped L Q x) R).xs.Nodup ∧
        ∀ z ∈ (tRun flipL (L ++ flipL x :: x :: Q).length (capped L Q x) R).xs,
          ¬ z.IsDiag) ∧
      (tCrit flipL (L ++ flipL x :: x :: Q).length (capped L Q x)
        [2 * Q.length + 2] R).Nodup := by
  simp only [StrictReduced₂, Reduced₂, critPts₂, run_cap, crit_cap]

end OddMath.SKM.SourceCapState
