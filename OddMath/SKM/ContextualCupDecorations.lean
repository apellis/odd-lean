import OddMath.SKM.PointedMatching

/-! Literal residual serializers followed by an isolated contextual cup. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove
variable {I : Type*}

@[simp] theorem tRen_append_cup (k p : ℕ) (x : Letter I) (T : TState (Letter I))
    (R : List (TMove (Letter I))) (j : ℕ) :
    tRen k T (R ++ [.mv (.cup p x)]) j = tRen k T R j := by
  induction R generalizing T j with
  | nil => rfl
  | cons m R ih => exact ih _ _

theorem target_cup_bound {a P Q : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (P ++ Q) R) : a.length + P.length ≤ (pairing₂ a R).length := by
  have he := congrArg List.length hR.pairing_properties.2.2
  simp only [List.length_map, List.length_append, length_dualW] at he
  omega

/-- Every old point remains on its residual strand after insertion of the
isolated cup, with the actual order-preserving endpoint index shift. -/
theorem onStrand_append_cup {a P Q : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (P ++ Q) R) (ε : Bool) (i : I)
    {j : ℕ} {q : ℕ × ℕ} (hq : q.1 ≤ R.length) (hj : OnStrand₂ a R j q) :
    OnStrand₂ a (R ++ [.mv (.cup P.length (ε, i))]) (rmIdx (a.length + P.length) j) q := by
  have ht : (R ++ [TMove.mv (.cup P.length (ε, i))]).take q.1 = R.take q.1 :=
    List.take_append_of_le_length hq
  have hd : (R ++ [TMove.mv (.cup P.length (ε, i))]).drop q.1 =
      R.drop q.1 ++ [.mv (.cup P.length (ε, i))] := List.drop_append_of_le_length hq
  constructor
  · simpa only [ht] using hj.1
  · rw [ht, hd, tRen_append_cup, pairing_append_cup]
    change _ = (idAt (insAt (pairing₂ a R) (a.length + P.length) _ _)
      (insIdx (a.length + P.length) j)).getD 0
    rw [idAt_insAt_insIdx (target_cup_bound hR)]
    exact hj.2

/-- Independent dot count on the new cup plus all old strand counts. -/
def terminalCupCountsEquiv {a P Q : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (P ++ Q) R) (ε : Bool) (i : I) :
    (MatchingStrand a (R ++ [.mv (.cup P.length (ε, i))]) → ℕ) ≃
      (ℕ × (MatchingStrand a R → ℕ)) := by
  have hp := cup_inserted_properties a P Q ε i hR
  have hv : Valid (pairing₂ a (R ++ [.mv (.cup P.length (ε, i))])) := by
    rw [pairing_append_cup]; exact hp.1
  have hc : Same (pairing₂ a (R ++ [.mv (.cup P.length (ε, i))]))
      (a.length + P.length) (a.length + P.length + 1) := by
    rw [pairing_append_cup]; exact hp.2.2.2.1
  exact capLabelEquiv hv hc (by rw [pairing_append_cup, hp.2.2.2.2]; exact Iso.refl _)

/-- Append exactly the cup and its dots; no old serializer is normalized. -/
def cupDecoratedMoves (P : List (Letter I)) (ε : Bool) (i : I) (b : ℕ)
    (ds : List (DTMove I)) : List (DTMove I) :=
  ds ++ [.tm (.mv (.cup P.length (ε, i)))] ++
    List.replicate b (.dt (if ε then P.length else P.length + 1))

@[simp] theorem dotPts_append (ds es : List (DTMove I)) :
    dotPts (ds ++ es) = dotPts ds ++ (dotPts es).map (fun q => (q.1 + (tmoves ds).length, q.2)) := by
  induction ds with
  | nil =>
      simp only [List.nil_append, dotPts, tmoves, List.length_nil, Nat.add_zero, Prod.mk.eta]
      exact (List.map_id _).symm
  | cons d ds ih =>
      cases d with
      | dt j => simp only [List.cons_append, dotPts, tmoves, ih]
      | tm m =>
          simp only [List.cons_append, dotPts, tmoves, ih, List.map_append,
            List.map_map, List.length_cons, Function.comp_def]
          congr 2

@[simp] theorem tmoves_replicate_dt (b p : ℕ) :
    tmoves (List.replicate b (DTMove.dt (I := I) p)) = [] := by
  induction b with
  | zero => rfl
  | succ b ih => simpa only [List.replicate_succ, tmoves] using ih

@[simp] theorem dotPts_replicate_dt (b p : ℕ) :
    dotPts (List.replicate b (DTMove.dt (I := I) p)) = List.replicate b (0, p) := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [List.replicate_succ, dotPts, ih]

@[simp] theorem tmoves_cupDecoratedMoves (P : List (Letter I)) (ε : Bool) (i : I) (b : ℕ)
    (ds : List (DTMove I)) :
    tmoves (cupDecoratedMoves P ε i b ds) = tmoves ds ++ [.mv (.cup P.length (ε, i))] := by
  simp only [cupDecoratedMoves, tmoves_append, tmoves_tm, tmoves_replicate_dt, List.append_nil]

 theorem dotPts_cupDecoratedMoves (P : List (Letter I)) (ε : Bool) (i : I) (b : ℕ)
    (ds : List (DTMove I)) :
    dotPts (cupDecoratedMoves P ε i b ds) = dotPts ds ++
      List.replicate b ((tmoves ds).length + 1, if ε then P.length else P.length + 1) := by
  rw [cupDecoratedMoves, dotPts_append, dotPts_append_tm]
  simp only [dotPts_replicate_dt,
    tmoves_append, tmoves_tm, List.length_append, List.length_singleton,
    List.map_replicate, Nat.zero_add]

 theorem dLay_cupDecoratedMoves {a P Q : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (P ++ Q) R) (ε : Bool) (i : I) (b : ℕ)
    {ds : List (DTMove I)} (hd : tmoves ds = R) :
    dLay a (cupDecoratedMoves P ε i b ds) = dLay a ds ++
      (xCupL (ε, i)).map (xwhL P Q) ++
      dLay (P ++ (ε, i) :: (!ε, i) :: Q)
        (List.replicate b (.dt (if ε then P.length else P.length + 1))) := by
  rw [cupDecoratedMoves, dLay_append, dLay_append, hd, hR.2,
    tmoves_append, hd, tmoves_tm, List.foldl_append]
  simp only [dLay, tmLay, moveLay_cup, List.append_nil, List.foldl_cons,
    List.foldl_nil, tLet, chStep_cup, hR.2]
  rfl

 theorem onStrand_terminal_cup {a P Q : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (P ++ Q) R) (ε : Bool) (i : I) :
    OnStrand₂ a (R ++ [.mv (.cup P.length (ε, i))]) (a.length + P.length)
      (R.length + 1, if ε then P.length else P.length + 1) := by
  have hC := matching_append_cup a P Q ε i hR
  have hl : R.length + 1 = (R ++ [TMove.mv (.cup P.length (ε, i))]).length := by simp
  rw [hl]
  constructor
  · simp only [List.take_length, hC.2]
    cases ε <;> simp
  · simp only [List.take_length, List.drop_length, tRen, id_eq]
    change idD (pairing₂ a (R ++ [.mv (.cup P.length (ε, i))]))
      (a.length + if ε then P.length else P.length + 1) =
      idD (pairing₂ a (R ++ [.mv (.cup P.length (ε, i))])) (a.length + P.length)
    simp only [pairing_append_cup, cupInsertedPairing, idD]
    have hb := target_cup_bound hR
    change a.length + P.length ≤ (tRun flipL a.length (tStart a) R).st.length at hb
    simp only [idAt_insAt hb]
    cases ε <;> simp [Nat.add_assoc]

def terminalCupStrandEquiv {a P Q : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (P ++ Q) R) (ε : Bool) (i : I) :
    MatchingStrand a (R ++ [.mv (.cup P.length (ε, i))]) ≃ Unit ⊕ MatchingStrand a R := by
  have hp := cup_inserted_properties a P Q ε i hR
  have hv : Valid (pairing₂ a (R ++ [.mv (.cup P.length (ε, i))])) := by
    rw [pairing_append_cup]; exact hp.1
  have hc : Same (pairing₂ a (R ++ [.mv (.cup P.length (ε, i))]))
      (a.length + P.length) (a.length + P.length + 1) := by
    rw [pairing_append_cup]; exact hp.2.2.2.1
  exact matchingStrandEquivOfCap hv hc (by
    rw [pairing_append_cup, hp.2.2.2.2]; exact Iso.refl _)

theorem rmIdx_ne_position (p j : ℕ) : rmIdx p j ≠ p := by
  unfold rmIdx
  split_ifs <;> omega

theorem leftEnds_append_cup_perm {a P Q : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (P ++ Q) R) (ε : Bool) (i : I) :
    (leftEnds₂ a (R ++ [.mv (.cup P.length (ε, i))])).Perm
      ((a.length + P.length) :: (leftEnds₂ a R).map (rmIdx (a.length + P.length))) := by
  let e := terminalCupStrandEquiv hR ε i
  have hn : (((a.length + P.length) ::
      (leftEnds₂ a R).map (rmIdx (a.length + P.length))) : List ℕ).Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · rintro hj
      obtain ⟨j, _, he⟩ := List.mem_map.mp hj
      exact rmIdx_ne_position _ _ he
    · exact (nodup_leftEnds₂ a R).map (fun _ _ h => rmIdx_inj.mp h)
  apply (List.perm_ext_iff_of_nodup (nodup_leftEnds₂ _ _) hn).mpr
  intro j
  simp only [List.mem_cons, List.mem_map]
  constructor
  · intro hj
    have he := congrArg Subtype.val (e.symm_apply_apply ⟨j, hj⟩)
    cases hz : e ⟨j, hj⟩ with
    | inl u =>
        cases u
        rw [hz] at he
        exact Or.inl he.symm
    | inr z =>
        rw [hz] at he
        exact Or.inr ⟨z.val, z.property, he⟩
  · rintro (rfl | ⟨z, hz, rfl⟩)
    · exact (e.symm (Sum.inl ())).property
    · exact (e.symm (Sum.inr ⟨z, hz⟩)).property

def cupPoints (a P : List (Letter I)) (R : List (TMove (Letter I))) (ε : Bool)
    (q : ℕ → ℕ × ℕ) (j : ℕ) : ℕ × ℕ :=
  if j = a.length + P.length then (R.length + 1, if ε then P.length else P.length + 1)
  else q (capDown (a.length + P.length) j)

def cupCounts (a P : List (Letter I)) (b : ℕ) (n : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j = a.length + P.length then b else n (capDown (a.length + P.length) j)

/-- The literal residual decoration followed by cup dots has exactly the
transported old counts and the separately prescribed new count. -/
theorem decorates_cupDecoratedMoves {a P Q : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a (P ++ Q) R) (ε : Bool) (i : I) (b : ℕ)
    {q : ℕ → ℕ × ℕ} {n : ℕ → ℕ} {ds : List (DTMove I)} (hd : Decorates₂ a R q n ds) :
    Decorates₂ a (R ++ [.mv (.cup P.length (ε, i))])
      (cupPoints a P R ε q) (cupCounts a P b n) (cupDecoratedMoves P ε i b ds) := by
  constructor
  · rw [tmoves_cupDecoratedMoves, hd.1]
  · rw [dotPts_cupDecoratedMoves, hd.1]
    have hp := (leftEnds_append_cup_perm hR ε i).flatMap_right
      (fun j => List.replicate (cupCounts a P b n j) (cupPoints a P R ε q j))
    simp only [List.flatMap_cons, List.flatMap_map,
      cupPoints, cupCounts, ite_eq_right (rmIdx_ne_position _ _), capDown_rmIdx] at hp
    exact ((hd.2.append_right _).trans List.perm_append_comm).trans hp.symm

end OddMath.SKM
