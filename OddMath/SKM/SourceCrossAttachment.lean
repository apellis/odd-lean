import OddMath.SKM.SourceCrossState
import OddMath.SKM.SourceCapAttachment
import OddMath.SKM.AdaptedPointedPair

/-! # Actual initial-crossing attachment

For arbitrary source contexts `L`, `Q` and target `b`, a strict residual
matching in the nonpaired, noninterleaving sector admits one literal initial
crossing. The proof follows `SourceCrossState.cross_run`, including the initial
crossing's cap-renamed history, and uses crossing parity to exclude duplication.
Frozen endpoint positions are `Q.length`, `Q.length + 1`; the initial ID
transposition is `exchangeId Q.length`, including when `Q` is empty.

`attach` retains the residual serializer, shifts its existing points by one
height, and transports counts along the actual endpoint transposition.
`exists_adapted_pointed_pair` chooses the low side and covers both orientations.
-/
noncomputable section
namespace OddMath.SKM.SourceCrossAttachment
open StringDiagrams StringDiagrams.Chord DTMove
open SourceCrossState
variable {I : Type*}

theorem matching (L Q b : List (Letter I)) (x y : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ y :: x :: Q) b R) :
    IsMatching₂ (L ++ x :: y :: Q) b (.mv (.cross L.length) :: R) := by
  refine ⟨cross_fits L Q x y R hR.1, ?_⟩
  simpa only [List.foldl_cons, tLet, chStep_cross] using hR.2

theorem pairing (L Q : List (Letter I)) (x y : Letter I)
    {R : List (TMove (Letter I))}
    (hR : TFits flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) R) :
    pairing₂ (L ++ x :: y :: Q) (.mv (.cross L.length) :: R) =
      (swapAt (pairing₂ (L ++ y :: x :: Q) R) Q.length).map
        (SourceIdRelabel.idMap (exchangeId Q.length)) := by
  unfold pairing₂
  rw [cross_run L Q x y R hR]
  rfl

private theorem iso_map (f : ℕ → ℕ) (hf : Function.Injective f)
    (s : List (ℕ × Letter I)) : Iso (s.map (SourceIdRelabel.idMap f)) s := by
  refine ⟨by simp [List.map_map, Function.comp_def, SourceIdRelabel.idMap], ?_⟩
  intro i j
  simp only [Same, idAt, List.getElem?_map, Option.map_map]
  change (i ≠ j ∧ (s[i]?).map (f ∘ Prod.fst) ≠ none ∧
    (s[i]?).map (f ∘ Prod.fst) = (s[j]?).map (f ∘ Prod.fst)) ↔ _
  simp only [← Option.map_map]
  cases h₁ : (s[i]?).map Prod.fst <;> cases h₂ : (s[j]?).map Prod.fst <;>
    simp [hf.eq_iff]

theorem pairing_iso (L Q : List (Letter I)) (x y : Letter I)
    {R : List (TMove (Letter I))}
    (hR : TFits flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) R) :
    Iso (pairing₂ (L ++ x :: y :: Q) (.mv (.cross L.length) :: R))
      (swapAt (pairing₂ (L ++ y :: x :: Q) R) Q.length) := by
  rw [pairing L Q x y hR]
  exact iso_map _ (exchangeId Q.length).injective _

/-- A frozen endpoint follows precisely the cap-renaming function. -/
private theorem frozen_id (k : ℕ) (T : TState (Letter I))
    (R : List (TMove (Letter I))) (hR : TFits flipL k T R)
    {p : ℕ} (hp : p < k) (hb : p < T.st.length) :
    idD (tRun flipL k T R).st p = tRen k T R (idD T.st p) := by
  induction R generalizing T with
  | nil => rfl
  | cons m R ih =>
    have cap_bound {g : ℕ} (h : (TMove.cap g).Ok flipL k T.st) :
        k + g + 1 < T.st.length := by
      obtain ⟨A, B, hA, hB, _⟩ := h
      by_contra hn
      rw [List.getElem?_eq_none (by omega)] at hB
      cases hB
    have hlen : p < (tStep flipL k T m).st.length := by
      cases m with
      | mv m =>
        cases m with
        | cup g a =>
          change p < (insAt T.st (k + g) _ _).length
          rw [length_insAt _ hR.1]
          omega
        | cross g => simpa only [tStep, length_swapAt] using hb
      | cap g =>
        change p < (jn T.st (k + g)).length
        rw [length_jn (cap_bound hR.1)]
        have := cap_bound hR.1
        omega
    change idD (tRun flipL k (tStep flipL k T m) R).st p =
      tRen k (tStep flipL k T m) R (stepRen k T m (idD T.st p))
    rw [ih _ hR.2 hlen]
    congr 1
    cases m with
    | mv m =>
      cases m with
      | cup g a =>
        simp only [tStep, stepRen]
        rw [idD, idAt_insAt hR.1]
        split_ifs <;> first | rfl | omega
      | cross g =>
        simp only [tStep, stepRen, idD]
        rw [idAt_swapAt hR.1]
        rw [tau_of_ne (by omega) (by omega)]
        rfl
    | cap g =>
      simp only [tStep, stepRen, idD]
      rw [idAt_jn' (cap_bound hR.1)]
      have he : rmIdx (k + g) p = p := by simp [rmIdx, show p < k + g by omega]
      rw [he, idAt_eq_idD hb]
      rfl

theorem source_bound {L Q b : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ y :: x :: Q) b R) :
    Q.length + 1 < (pairing₂ (L ++ y :: x :: Q) R).length := by
  have h := congrArg List.length hR.pairing_properties.2.2
  simp only [List.length_map, List.length_append, List.length_cons, length_dualW] at h
  omega

private theorem initial_ids (L Q : List (Letter I)) (x y : Letter I) :
    idD (tStart (L ++ y :: x :: Q)).st Q.length = 2 * Q.length ∧
    idD (tStart (L ++ y :: x :: Q)).st (Q.length + 1) = 2 * Q.length + 2 := by
  rw [start_st]
  have hlen : (SourceCapState.before Q).length = Q.length := by
    simp [SourceCapState.before, SourceCapState.indexed, length_dualW]
  simp only [List.append_assoc]
  simp [idD, idAt, hlen]

private theorem final_ids (L Q : List (Letter I)) (x y : Letter I)
    {R : List (TMove (Letter I))}
    (hR : TFits flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) R) :
    idD (pairing₂ (L ++ y :: x :: Q) R) Q.length =
      tRen (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) R (2 * Q.length) ∧
    idD (pairing₂ (L ++ y :: x :: Q) R) (Q.length + 1) =
      tRen (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) R (2 * Q.length + 2) := by
  have hlen : Q.length + 1 < (tStart (L ++ y :: x :: Q)).st.length := by
    simp [tStart, run_cupMoves, length_cupLeft, length_dualW]
    omega
  constructor
  · rw [pairing₂, frozen_id _ _ _ hR (by simp only [List.length_append, List.length_cons]; omega) (by omega), (initial_ids L Q x y).1]
  · rw [pairing₂, frozen_id _ _ _ hR (by simp only [List.length_append, List.length_cons]; omega) hlen, (initial_ids L Q x y).2]

/-- Noninterleaving distinct source strands admit one actual initial crossing. -/
theorem strict {L Q b : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ y :: x :: Q) b R)
    (hr : StrictReduced₂ (L ++ y :: x :: Q) R)
    (hn : ¬ Same (pairing₂ (L ++ y :: x :: Q) R) Q.length (Q.length + 1))
    (hi : ¬ Ilv (pairing₂ (L ++ y :: x :: Q) R) Q.length) :
    StrictReduced₂ (L ++ x :: y :: Q) (.mv (.cross L.length) :: R) := by
  have hb := source_bound hR
  have h₀ := idAt_eq_idD (show Q.length < (pairing₂ (L ++ y :: x :: Q) R).length by omega)
  have h₁ := idAt_eq_idD hb
  have hne : idD (pairing₂ (L ++ y :: x :: Q) R) Q.length ≠
      idD (pairing₂ (L ++ y :: x :: Q) R) (Q.length + 1) := by
    intro he
    exact hn ⟨by omega, by rw [h₀]; simp, by rw [h₀, h₁, he]⟩
  have hnot : s(idD (pairing₂ (L ++ y :: x :: Q) R) Q.length,
      idD (pairing₂ (L ++ y :: x :: Q) R) (Q.length + 1)) ∉
      (tRun flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) R).xs := by
    intro hm
    exact hi ((ilv2_iff_ilv hR.pairing_properties.1 h₀ h₁).mp
      ((mem_xs_iff ((tInv_tStart _).run hR.1) hr.1 hne).mp hm))
  have hid := final_ids L Q x y hR.1
  constructor
  · change CrossOnce (tRun flipL _ _ _)
    rw [cross_run L Q x y R hR.1, ← hid.1, ← hid.2]
    change ([s(exchangeId Q.length _, exchangeId Q.length _)] ++
      ((tRun flipL _ _ R).xs.map (Sym2.map (exchangeId Q.length)))).Nodup ∧ _
    constructor
    · apply (List.nodup_cons).mpr
      refine ⟨?_, hr.1.1.map (Sym2.map.injective (exchangeId Q.length).injective)⟩
      intro hm
      obtain ⟨z, hz, he⟩ := List.mem_map.mp hm
      have he' : Sym2.map (exchangeId Q.length) z = Sym2.map (exchangeId Q.length)
          s(idD (pairing₂ (L ++ y :: x :: Q) R) Q.length,
            idD (pairing₂ (L ++ y :: x :: Q) R) (Q.length + 1)) := he
      exact hnot ((Sym2.map.injective (exchangeId Q.length).injective he') ▸ hz)
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · intro hd
        exact hne ((exchangeId Q.length).injective (Sym2.mk_isDiag_iff.mp hd))
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
        exact fun hd => hr.1.2 w hw ((Sym2.isDiag_map (exchangeId Q.length).injective).mp hd)
  · change (tCrit flipL _ _ [] _).Nodup
    rw [cross_crit L Q x y R hR.1]
    exact hr.2.map (exchangeId Q.length).injective

private theorem next_run_le (k : ℕ) (T : TState (Letter I)) (R : List (TMove (Letter I))) :
    T.nxt ≤ (tRun flipL k T R).nxt := by
  induction R generalizing T with
  | nil => exact le_rfl
  | cons m R ih =>
    have hs : T.nxt ≤ (tStep flipL k T m).nxt := by
      cases m with
      | mv m => cases m <;> simp [tStep]
      | cap g => exact le_rfl
    exact hs.trans (ih _)

private theorem run_length (a : List (Letter I)) (R : List (TMove (Letter I)))
    (hR : TFits flipL a.length (tStart a) R) :
    (tRun flipL a.length (tStart a) R).st.length = a.length + (R.foldl tLet a).length := by
  have h := congrArg List.length (letters_tRun (length_dualW a) R (tStart a) a (tStart_letters a) hR)
  simpa [length_dualW] using h

private theorem idD_map (f : ℕ → ℕ) (s : List (ℕ × Letter I)) (j : ℕ) (hj : j < s.length) :
    idD (s.map (SourceIdRelabel.idMap f)) j = f (idD s j) := by
  simp [idD, idAt, List.getElem?_eq_getElem hj, SourceIdRelabel.idMap]

private theorem ren_after_prefix (L Q : List (Letter I)) (x y : Letter I)
    (P R : List (TMove (Letter I)))
    (hR : TFits flipL (L ++ y :: x :: Q).length
      (tRun flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) P) R)
    (xs : List (Sym2 ℕ)) (z : ℕ) :
    tRen (L ++ y :: x :: Q).length
      (history xs (SourceIdRelabel.rename (exchangeId Q.length)
        (SourceFrozenSwap.frozen Q.length
          (tRun flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) P))))
      R (exchangeId Q.length z) =
      exchangeId Q.length (tRen (L ++ y :: x :: Q).length
        (tRun flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) P) R z) := by
  have hfix : ∀ n, (tRun flipL (L ++ y :: x :: Q).length
      (tStart (L ++ y :: x :: Q)) P).nxt ≤ n → exchangeId Q.length n = n := by
    intro n hn
    have hh := (next_run_le (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) P).trans hn
    simp only [tStart, run_cupMoves, List.length_append, List.length_map,
      List.length_reverse, length_cupLeft, length_dualW, List.length_cons] at hh
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  rw [history_ren, SourceIdRelabel.ren _ (exchangeId Q.length).injective _
    (SourceFrozenSwap.frozen Q.length
      (tRun flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) P)) hfix R
    (SourceFrozenSwap.fits flipL (by simp) _ _ hR) z,
    SourceFrozenSwap.ren (by simp) _ _ hR z]

/-- Existing points are shifted by one height, not chosen afresh. -/
theorem onStrand (L Q : List (Letter I)) (x y : Letter I)
    (R : List (TMove (Letter I)))
    (hR : TFits flipL (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q)) R)
    {j : ℕ} (hj : j < (pairing₂ (L ++ y :: x :: Q) R).length) {q : ℕ × ℕ}
    (hq : OnStrand₂ (L ++ y :: x :: Q) R j q) :
    OnStrand₂ (L ++ x :: y :: Q) (.mv (.cross L.length) :: R)
      (tau Q.length j) (q.1 + 1, q.2) := by
  have hs := (tFits_append_at (L ++ y :: x :: Q).length (tStart (L ++ y :: x :: Q))
    (R.take q.1) (R.drop q.1)).mp (by simpa using hR)
  have hlen : (L ++ x :: y :: Q).length = (L ++ y :: x :: Q).length := by simp
  have hp : Q.length + 1 < (pairing₂ (L ++ y :: x :: Q) (R.take q.1)).length := by
    rw [pairing₂, run_length _ _ hs.1]
    simp only [List.length_append, List.length_cons]
    omega
  have hf : Q.length + 1 < (pairing₂ (L ++ y :: x :: Q) R).length := by
    rw [pairing₂, run_length _ _ hR]
    simp only [List.length_append, List.length_cons]
    omega
  have ha : (L ++ y :: x :: Q).length + q.2 <
      (pairing₂ (L ++ y :: x :: Q) (R.take q.1)).length := by
    rw [pairing₂, run_length _ _ hs.1]
    exact Nat.add_lt_add_left hq.1 _
  constructor
  · simpa only [List.take_succ_cons, List.foldl_cons, tLet, chStep_cross] using hq.1
  · change tRen _ (tRun flipL _ _ ((.mv (.cross L.length) :: R).take (q.1 + 1)))
      ((.mv (.cross L.length) :: R).drop (q.1 + 1))
      (idD (pairing₂ (L ++ x :: y :: Q) ((.mv (.cross L.length) :: R).take (q.1 + 1)))
        ((L ++ x :: y :: Q).length + q.2)) = _
    rw [List.take_succ_cons, List.drop_succ_cons, pairing L Q x y hs.1,
      pairing L Q x y hR, hlen, idD_map _ _ _ (by simpa only [length_swapAt] using ha),
      idD_map _ _ _ (by rw [length_swapAt]; unfold tau; split_ifs <;> omega)]
    have ht : tau Q.length ((L ++ y :: x :: Q).length + q.2) =
        (L ++ y :: x :: Q).length + q.2 :=
      tau_of_ne (by simp only [List.length_append, List.length_cons]; omega)
        (by simp only [List.length_append, List.length_cons]; omega)
    rw [show idD (swapAt (pairing₂ (L ++ y :: x :: Q) (R.take q.1)) Q.length)
        ((L ++ y :: x :: Q).length + q.2) =
        idD (pairing₂ (L ++ y :: x :: Q) (R.take q.1))
          ((L ++ y :: x :: Q).length + q.2) by simp only [idD, idAt_swapAt hp, ht]]
    rw [show idD (swapAt (pairing₂ (L ++ y :: x :: Q) R) Q.length) (tau Q.length j) =
        idD (pairing₂ (L ++ y :: x :: Q) R) j by simp only [idD, idAt_swapAt hf, tau_tau]]
    rw [← hlen, cross_run L Q x y (R.take q.1) hs.1, hlen,
      ren_after_prefix L Q x y _ _ hs.2]
    exact congrArg (exchangeId Q.length) hq.2

/-- Actual endpoint transposition, including its reversal on the source boundary. -/
def labelEquiv {L Q b : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ y :: x :: Q) b R)
    (hn : ¬ Same (pairing₂ (L ++ y :: x :: Q) R) Q.length (Q.length + 1)) :
    MatchingStrand (L ++ y :: x :: Q) R ≃
      MatchingStrand (L ++ x :: y :: Q) (.mv (.cross L.length) :: R) :=
  matchingStrandEquivOfSwap (source_bound hR) hn (pairing_iso L Q x y hR.1)

@[simp] theorem labelEquiv_val {L Q b : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ y :: x :: Q) b R)
    (hn : ¬ Same (pairing₂ (L ++ y :: x :: Q) R) Q.length (Q.length + 1))
    (j : MatchingStrand (L ++ y :: x :: Q) R) :
    (labelEquiv hR hn j).val = tau Q.length j.val := rfl

def countsEquiv {L Q b : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ y :: x :: Q) b R)
    (hn : ¬ Same (pairing₂ (L ++ y :: x :: Q) R) Q.length (Q.length + 1)) :
    (MatchingStrand (L ++ y :: x :: Q) R → ℕ) ≃
      (MatchingStrand (L ++ x :: y :: Q) (.mv (.cross L.length) :: R) → ℕ) :=
  Equiv.arrowCongr (labelEquiv hR hn) (Equiv.refl ℕ)

private theorem ends_perm {L Q b : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ y :: x :: Q) b R)
    (hn : ¬ Same (pairing₂ (L ++ y :: x :: Q) R) Q.length (Q.length + 1)) :
    (leftEnds₂ (L ++ x :: y :: Q) (.mv (.cross L.length) :: R)).Perm
      ((leftEnds₂ (L ++ y :: x :: Q) R).map (tau Q.length)) := by
  apply (List.perm_ext_iff_of_nodup (nodup_leftEnds₂ _ _)
    ((nodup_leftEnds₂ _ _).map (fun _ _ h => tau_inj.mp h))).mpr
  intro j
  constructor
  · intro hj
    let z := (labelEquiv hR hn).symm ⟨j, hj⟩
    exact List.mem_map.mpr ⟨z.val, z.property,
      congrArg Subtype.val ((labelEquiv hR hn).apply_symm_apply ⟨j, hj⟩)⟩
  · intro hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    exact (labelEquiv hR hn ⟨i, hi⟩).property

private theorem counts_transport {L Q b : List (Letter I)} {x y : Letter I}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ y :: x :: Q) b R)
    (hn : ¬ Same (pairing₂ (L ++ y :: x :: Q) R) Q.length (Q.length + 1))
    (n : MatchingStrand (L ++ x :: y :: Q) (.mv (.cross L.length) :: R) → ℕ)
    (j : ℕ) : strandCounts (n ∘ labelEquiv hR hn) (tau Q.length j) = strandCounts n j := by
  classical
  have he : j ∈ leftEnds₂ (L ++ x :: y :: Q) (.mv (.cross L.length) :: R) ↔
      tau Q.length j ∈ leftEnds₂ (L ++ y :: x :: Q) R := by
    rw [(ends_perm hR hn).mem_iff, List.mem_map]
    constructor
    · rintro ⟨i, hi, rfl⟩; simpa only [tau_tau] using hi
    · intro h; exact ⟨_, h, tau_tau _ _⟩
  by_cases hj : j ∈ leftEnds₂ (L ++ x :: y :: Q) (.mv (.cross L.length) :: R)
  · rw [strandCounts, dite_eq_left (he.mp hj), strandCounts, dite_eq_left hj]
    apply congrArg n
    exact Subtype.ext (tau_tau _ _)
  · simp only [strandCounts, dite_eq_right hj, dite_eq_right (fun h => hj (he.mpr h))]

/-- Prepend one crossing, preserving every residual point and serializer. -/
def attach {L Q b : List (Letter I)} {x y : Letter I}
    (F : PointedMatching (L ++ y :: x :: Q) b)
    (hn : ¬ Same (pairing₂ (L ++ y :: x :: Q) F.moves) Q.length (Q.length + 1))
    (hi : ¬ Ilv (pairing₂ (L ++ y :: x :: Q) F.moves) Q.length) :
    PointedMatching (L ++ x :: y :: Q) b := by
  let e := labelEquiv F.matching hn
  refine ⟨.mv (.cross L.length) :: F.moves, matching L Q b x y F.matching,
    strict F.matching F.strict hn hi,
    fun j => ((F.points (tau Q.length j)).1 + 1, (F.points (tau Q.length j)).2), ?_, ?_,
    fun n => .tm (.mv (.cross L.length)) :: F.serialize (n ∘ e), ?_⟩
  · intro j hj
    have hb := F.bounded (e.symm ⟨j, hj⟩).val (e.symm ⟨j, hj⟩).property
    change (F.points (tau Q.length j)).1 ≤ F.moves.length at hb
    simp only [List.length_cons]
    omega
  · intro j hj
    let z := e.symm ⟨j, hj⟩
    have h := onStrand L Q x y F.moves F.matching.1
      (mem_leftEnds₂.mp z.property).1 (F.onStrand z.val z.property)
    have hz : z.val = tau Q.length j := rfl
    simpa only [hz, tau_tau] using h
  · intro n
    constructor
    · change _ :: tmoves (F.serialize (n ∘ e)) = _
      rw [(F.decorates (n ∘ e)).1]
    · change ((dotPts (F.serialize (n ∘ e))).map (fun p => (p.1 + 1, p.2))).Perm _
      apply ((F.decorates (n ∘ e)).2.map (fun p => (p.1 + 1, p.2))).trans
      have hp := (ends_perm F.matching hn).flatMap_right
        (fun j => List.replicate (strandCounts n j)
          ((F.points (tau Q.length j)).1 + 1, (F.points (tau Q.length j)).2))
      apply List.Perm.trans _ hp.symm
      simp only [List.map_flatMap, List.map_replicate, List.flatMap_map, Function.comp_def, tau_tau]
      apply List.Perm.of_eq
      apply List.flatMap_congr
      intro j _
      have hc := counts_transport F.matching hn n (tau Q.length j)
      simpa only [tau_tau, e, Function.comp_def] using congrArg
        (fun c => List.replicate c ((F.points j).1 + 1, (F.points j).2)) hc

@[simp] theorem attach_moves {L Q b : List (Letter I)} {x y : Letter I}
    (F : PointedMatching (L ++ y :: x :: Q) b)
    (hn : ¬ Same (pairing₂ (L ++ y :: x :: Q) F.moves) Q.length (Q.length + 1))
    (hi : ¬ Ilv (pairing₂ (L ++ y :: x :: Q) F.moves) Q.length) :
    (attach F hn hi).moves = .mv (.cross L.length) :: F.moves := rfl

@[simp] theorem attach_points {L Q b : List (Letter I)} {x y : Letter I}
    (F : PointedMatching (L ++ y :: x :: Q) b)
    (hn : ¬ Same (pairing₂ (L ++ y :: x :: Q) F.moves) Q.length (Q.length + 1))
    (hi : ¬ Ilv (pairing₂ (L ++ y :: x :: Q) F.moves) Q.length) (j : ℕ) :
    (attach F hn hi).points j =
      ((F.points (tau Q.length j)).1 + 1, (F.points (tau Q.length j)).2) := rfl

@[simp] theorem attach_serialize {L Q b : List (Letter I)} {x y : Letter I}
    (F : PointedMatching (L ++ y :: x :: Q) b)
    (hn : ¬ Same (pairing₂ (L ++ y :: x :: Q) F.moves) Q.length (Q.length + 1))
    (hi : ¬ Ilv (pairing₂ (L ++ y :: x :: Q) F.moves) Q.length)
    (n : MatchingStrand (L ++ x :: y :: Q) (attach F hn hi).moves → ℕ) :
    (attach F hn hi).serialize n =
      .tm (.mv (.cross L.length)) :: F.serialize (n ∘ labelEquiv F.matching hn) := rfl

theorem attach_layers_high {L Q b : List (Letter I)} {x y : Letter I}
    (F : PointedMatching (L ++ y :: x :: Q) b)
    (hn : ¬ Same (pairing₂ (L ++ y :: x :: Q) F.moves) Q.length (Q.length + 1))
    (hi : ¬ Ilv (pairing₂ (L ++ y :: x :: Q) F.moves) Q.length)
    (n : MatchingStrand (L ++ x :: y :: Q) (attach F hn hi).moves → ℕ) :
    (attach F hn hi).layers n = (xCrL x y).map (xwhL L Q) ++
      F.layers (n ∘ labelEquiv F.matching hn) := by
  change dLay _ (.tm (.mv (.cross L.length)) :: _) = _
  simp only [dLay, tmLay, moveLay_cross, tLet, chStep_cross]
  rfl

theorem attach_layers {L Q b : List (Letter I)} {x y : Letter I}
    (F : PointedMatching (L ++ y :: x :: Q) b)
    (hn : ¬ Same (pairing₂ (L ++ y :: x :: Q) F.moves) Q.length (Q.length + 1))
    (hi : ¬ Ilv (pairing₂ (L ++ y :: x :: Q) F.moves) Q.length)
    (n : MatchingStrand (L ++ y :: x :: Q) F.moves → ℕ) :
    (attach F hn hi).layers (n ∘ (labelEquiv F.matching hn).symm) =
      (xCrL x y).map (xwhL L Q) ++ F.layers n := by
  rw [attach_layers_high]
  congr 2
  funext j
  simp

theorem exists_strictReduced_source_swap (L Q b : List (Letter I)) (x y : Letter I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ (L ++ x :: y :: Q) b R) :
    ∃ S, IsMatching₂ (L ++ y :: x :: Q) b S ∧ StrictReduced₂ (L ++ y :: x :: Q) S ∧
      Iso (pairing₂ (L ++ y :: x :: Q) S)
        (swapAt (pairing₂ (L ++ x :: y :: Q) R) Q.length) := by
  obtain ⟨hv, hl, hs⟩ := hR.pairing_properties
  have hp := source_bound hR
  apply exists_strictReduced_matching (hv.swapAt hp)
    (hl.swapAt_of_involutive flipL_involutive hp)
  rw [map_swapAt, hs]
  simp only [dualW_append, dualW_cons, List.append_assoc, List.cons_append, List.nil_append]
  rw [← length_dualW Q, swapAt_mid]

/-- Both crossing orientations share actual pointed representatives and a
strand-count equivalence. The local crossing is prepended, never appended. -/
structure AdaptedPointedPair (L Q b : List (Letter I)) (x y : Letter I) where
  left : PointedMatching (L ++ x :: y :: Q) b
  right : PointedMatching (L ++ y :: x :: Q) b
  strands : MatchingStrand (L ++ x :: y :: Q) left.moves ≃
    MatchingStrand (L ++ y :: x :: Q) right.moves
  strands_val : ∀ j, (strands j).val = tau Q.length j.val
  swapped : Iso (pairing₂ (L ++ y :: x :: Q) right.moves)
    (swapAt (pairing₂ (L ++ x :: y :: Q) left.moves) Q.length)
  layers : ∀ n : MatchingStrand (L ++ x :: y :: Q) left.moves → ℕ,
    right.layers (n ∘ strands.symm) = (xCrL y x).map (xwhL L Q) ++ left.layers n ∨
    left.layers n = (xCrL x y).map (xwhL L Q) ++ right.layers (n ∘ strands.symm)
  literal : right.moves = .mv (.cross L.length) :: left.moves ∨
    left.moves = .mv (.cross L.length) :: right.moves

/-- Every distinct-source-endpoint class has adapted low/high representatives,
with no strictness or pairing hypothesis on the attached word. -/
theorem exists_adapted_pointed_pair (L Q b : List (Letter I)) (x y : Letter I)
    {T : List (TMove (Letter I))} (hT : IsMatching₂ (L ++ x :: y :: Q) b T)
    (hn : ¬ Same (pairing₂ (L ++ x :: y :: Q) T) Q.length (Q.length + 1)) :
    ∃ A : AdaptedPointedPair L Q b x y,
      Iso (pairing₂ (L ++ x :: y :: Q) A.left.moves) (pairing₂ (L ++ x :: y :: Q) T) := by
  classical
  by_cases hi : Ilv (pairing₂ (L ++ x :: y :: Q) T) Q.length
  · obtain ⟨S, hS, hrS, hs⟩ := exists_strictReduced_source_swap L Q b x y hT
    have hp := source_bound hT
    have hnS : ¬ Same (pairing₂ (L ++ y :: x :: Q) S) Q.length (Q.length + 1) := by
      intro h
      have hh := (hs.2 _ _).mp h
      rw [same_swapAt hp, tau_left, tau_right] at hh
      exact hn hh.symm
    have hiS : ¬ Ilv (pairing₂ (L ++ y :: x :: Q) S) Q.length := by
      rw [ilv_iff_of_iso hs, ilv_swapAt_iff hT.pairing_properties.1 hp hn]
      exact not_not_intro hi
    let G := PointedMatching.ofStrict hS hrS
    let F := attach G hnS hiS
    have hFG := pairing_iso L Q x y hS.1
    let A : AdaptedPointedPair L Q b x y :=
      { left := F
        right := G
        strands := (labelEquiv G.matching hnS).symm
        strands_val := fun _ => rfl
        swapped := by
          change Iso (pairing₂ (L ++ y :: x :: Q) S)
            (swapAt (pairing₂ (L ++ x :: y :: Q) (.mv (.cross L.length) :: S)) Q.length)
          simpa only [swapAt_swapAt] using (hFG.swapAt Q.length).symm
        layers := fun n => Or.inr (attach_layers_high G hnS hiS n)
        literal := Or.inr rfl }
    refine ⟨A, ?_⟩
    exact hFG.trans (by simpa only [swapAt_swapAt] using hs.swapAt Q.length)
  · obtain ⟨R, hR, hrR, hr⟩ := exists_strictReduced_matching
      hT.pairing_properties.1 hT.pairing_properties.2.1 hT.pairing_properties.2.2
    have hnR : ¬ Same (pairing₂ (L ++ x :: y :: Q) R) Q.length (Q.length + 1) :=
      fun h => hn ((hr.2 _ _).mp h)
    have hiR : ¬ Ilv (pairing₂ (L ++ x :: y :: Q) R) Q.length := by
      rwa [ilv_iff_of_iso hr]
    let F := PointedMatching.ofStrict hR hrR
    let G := attach F hnR hiR
    let A : AdaptedPointedPair L Q b x y :=
      { left := F
        right := G
        strands := labelEquiv F.matching hnR
        strands_val := fun _ => rfl
        swapped := pairing_iso L Q y x hR.1
        layers := fun n => Or.inl (attach_layers F hnR hiR n)
        literal := Or.inl rfl }
    exact ⟨A, hr⟩

end OddMath.SKM.SourceCrossAttachment
