import OddMath.SKM.CupAttachmentGrading
import OddMath.SKM.MatchingBending

/-! Literal cup attachment, supporting BE2 v2 Theorem 10.3 Claim 2.
No normalization or representative-family invariance is asserted. -/

namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove
variable {I : Type*}

/-- The literal underlying matching after the right cup is attached. -/
def cupAttachMatching (i : I) (R : List (TMove (Letter I))) : List (TMove (Letter I)) :=
  .mv (.cup 0 (false, i)) :: R.map (shiftT 1)

private theorem tStep_shift_at (k n : ℕ) (T : TState (Letter I)) (m : TMove (Letter I)) :
    tStep flipL k T (shiftT n m) = tStep flipL (k + n) T m := by
  rcases m with (⟨g, x⟩ | p) | g <;> simp [tStep, shiftT, shiftM, Nat.add_assoc]

private theorem tRun_shift_at (k n : ℕ) (T : TState (Letter I))
    (R : List (TMove (Letter I))) :
    tRun flipL k T (R.map (shiftT n)) = tRun flipL (k + n) T R := by
  induction R generalizing T with
  | nil => rfl
  | cons m R ih =>
    simp only [List.map_cons, tRun, List.foldl_cons]
    rw [tStep_shift_at]
    exact ih _

private theorem tFits_shift_at (k n : ℕ) (T : TState (Letter I))
    (R : List (TMove (Letter I))) :
    TFits flipL k T (R.map (shiftT n)) ↔ TFits flipL (k + n) T R := by
  induction R generalizing T with
  | nil => rfl
  | cons m R ih =>
    simp only [List.map_cons, TFits, tStep_shift_at, ih]
    rcases m with (⟨g, x⟩ | p) | g <;> simp [TMove.Ok, shiftT, shiftM, Nat.add_assoc]

private theorem fits_run_iso (k : ℕ) (R : List (TMove (Letter I)))
    {T U : TState (Letter I)} (hT : TInv T) (hU : TInv U) (hi : Iso T.st U.st)
    (hf : TFits flipL k U R) :
    TFits flipL k T R ∧ Iso (tRun flipL k T R).st (tRun flipL k U R).st := by
  induction R generalizing T U with
  | nil => exact ⟨trivial, hi⟩
  | cons m R ih =>
    have hm : m.Ok flipL k T.st := by
      cases m with
      | mv m => cases m <;> simpa only [TMove.Ok, hi.length_eq] using hf.1
      | cap g => exact okCap_of_iso hi hf.1
    have hs : Iso (tStep flipL k T m).st (tStep flipL k U m).st := by
      rcases m with (⟨g, x⟩ | p) | g
      · exact hi.insAt hm (fun z hz => (hT.fresh z hz).ne)
          (fun z hz => (hU.fresh z hz).ne) x (flipL x)
      · exact hi.swapAt (k + p)
      · apply hi.jn
        obtain ⟨A, B, _, hB, _, _⟩ := hm
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hB
        cases hB
    obtain ⟨hfit, hiso⟩ := ih (hT.step hm) (hU.step hf.1) hs hf.2
    exact ⟨⟨hm, hfit⟩, hiso⟩

/-- The initial cup produces exactly the same endpoint IDs as the old nested cups.
The next fresh ID need not agree, so this is intentionally a state-list equality only. -/
theorem cupAttach_start_st (i : I) (a : List (Letter I)) :
    (tStep flipL a.length (tStart a) (.mv (.cup 0 (false, i)))).st =
      (tStart ((true, i) :: a)).st := by
  simp only [tStart, tStep, Nat.add_zero, dualW_cons, flipL]
  rw [cupMoves_append, Chord.run_append]
  simp only [List.foldl_cons, List.foldl_nil, Chord.step, length_dualW]
  rfl

private theorem cupAttach_ok (i : I) (a : List (Letter I)) :
    (TMove.mv (.cup 0 (false, i))).Ok flipL a.length (tStart a).st := by
  have h := congrArg List.length (tStart_letters a)
  simp only [List.length_map, List.length_append, length_dualW] at h
  change a.length + 0 ≤ (tStart a).st.length
  omega

private theorem foldl_shift_prefix (u : List (Letter I)) (R : List (TMove (Letter I)))
    (k : ℕ) (T : TState (Letter I)) (v l : List (Letter I)) (hv : v.length = k)
    (hl : T.st.map Prod.snd = v ++ l) (hf : TFits flipL k T R) :
    (R.map (shiftT u.length)).foldl tLet (u ++ l) = u ++ R.foldl tLet l := by
  induction R generalizing T l with
  | nil => rfl
  | cons m R ih =>
    have hm : ∀ mm, m = .mv mm → mm.Ok l.length := by
      intro mm he
      subst he
      have hlen := congrArg List.length hl
      simp only [List.length_map, List.length_append, hv] at hlen
      cases mm with
      | cup g x => change g ≤ l.length; have : k + g ≤ T.st.length := hf.1; omega
      | cross p => change p + 1 < l.length; have : k + p + 1 < T.st.length := hf.1; omega
    have hn := letters_tRun hv [m] T l hl ⟨hf.1, trivial⟩
    simp only [tRun, List.foldl_cons, List.foldl_nil] at hn
    simp only [List.map_cons, List.foldl_cons]
    rw [← (tmLay_shift u hm).2]
    exact ih _ _ hn hf.2

/-- Literal cup attachment is a matching in the bent boundary class. -/
theorem cupAttach_matching_iso {i : I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ ((true, i) :: a) b R) :
    IsMatching₂ a ((false, i) :: b) (cupAttachMatching i R) ∧
      Iso (pairing₂ a (cupAttachMatching i R)) (pairing₂ ((true, i) :: a) R) := by
  let T := tStep flipL a.length (tStart a) (.mv (.cup 0 (false, i)))
  have hi : Iso T.st (tStart ((true, i) :: a)).st := by
    rw [show T.st = (tStart ((true, i) :: a)).st from cupAttach_start_st i a]
    exact Iso.refl _
  have hf := fits_run_iso (a.length + 1) R
    ((tInv_tStart a).step (cupAttach_ok i a)) (tInv_tStart ((true, i) :: a)) hi hR.1
  refine ⟨⟨⟨cupAttach_ok i a, (tFits_shift_at a.length 1 T R).2 hf.1⟩, ?_⟩, ?_⟩
  · have he := foldl_shift_prefix [(false, i)] R _ (tStart ((true, i) :: a))
      (dualW ((true, i) :: a)) ((true, i) :: a) (length_dualW _) (tStart_letters _) hR.1
    have hc : tLet a (.mv (.cup 0 (false, i))) = (false, i) :: (true, i) :: a := by
      simpa [tLet, flipL] using chStep_cup ([] : List (Letter I)) a (false, i)
    simpa only [cupAttachMatching, List.foldl_cons, hc, List.length_singleton,
      List.singleton_append, hR.2] using he
  · change Iso (tRun flipL a.length T (R.map (shiftT 1))).st _
    rw [tRun_shift_at]
    exact hf.2

/-- Endpoint-number equality, not merely a bijection of cardinalities. -/
theorem leftEnds₂_cupAttach {i : I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ ((true, i) :: a) b R) :
    leftEnds₂ a (cupAttachMatching i R) = leftEnds₂ ((true, i) :: a) R := by
  classical
  have hi := (cupAttach_matching_iso hR).2
  unfold leftEnds₂
  rw [hi.length_eq]
  congr 1
  funext j
  simp only [isLeftEnd_iso hi]

/-- The identity on ordered boundary endpoints gives the strand correspondence. -/
def cupAttachStrandEquiv {i : I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ ((true, i) :: a) b R) :
    MatchingStrand ((true, i) :: a) R ≃ MatchingStrand a (cupAttachMatching i R) where
  toFun j := ⟨j.val, by rw [leftEnds₂_cupAttach hR]; exact j.property⟩
  invFun j := ⟨j.val, by rw [← leftEnds₂_cupAttach hR]; exact j.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem cupAttachStrandEquiv_val {i : I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ ((true, i) :: a) b R)
    (j : MatchingStrand ((true, i) :: a) R) : (cupAttachStrandEquiv hR j).val = j.val := rfl

/-- The point after insertion of the cup and the leftmost vertical strand. -/
def cupAttachPoint (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + 1, p.2 + 1)

private theorem dotPts_shiftD (n : ℕ) (ds : List (DTMove I)) :
    dotPts (ds.map (shiftD n)) = (dotPts ds).map (fun p => (p.1, n + p.2)) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [shiftD, dotPts, ih, List.map_map, Function.comp_def]

@[simp] theorem dotPts_cupAttach (i : I) (ds : List (DTMove I)) :
    dotPts (cupAttachMoves i ds) = (dotPts ds).map cupAttachPoint := by
  simp [cupAttachMoves, dotPts, dotPts_shiftD, List.map_map, cupAttachPoint, Nat.add_comm]

/-- Decoration transport is the actual permutation of replicated distinguished points.
This statement does not by itself certify that the points lie on the named strands. -/
theorem decorates₂_cupAttach {i : I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ ((true, i) :: a) b R)
    (q : ℕ → ℕ × ℕ) (c : MatchingStrand ((true, i) :: a) R → ℕ)
    {ds : List (DTMove I)} (hd : Decorates₂ ((true, i) :: a) R q (strandCounts c) ds) :
    Decorates₂ a (cupAttachMatching i R) (cupAttachPoint ∘ q)
      (strandCounts (c ∘ (cupAttachStrandEquiv hR).symm)) (cupAttachMoves i ds) := by
  classical
  constructor
  · simp only [cupAttachMoves, tmoves, tmoves_map_shiftD, hd.1, cupAttachMatching]
  · rw [dotPts_cupAttach]
    have hp := hd.2.map cupAttachPoint
    rw [List.map_flatMap] at hp
    refine hp.trans (List.Perm.of_eq ?_)
    rw [leftEnds₂_cupAttach hR]
    apply List.flatMap_congr
    intro j hj
    have hj' : j ∈ leftEnds₂ a (cupAttachMatching i R) := by
      rw [leftEnds₂_cupAttach hR]; exact hj
    simp [List.map_replicate, strandCounts, hj, hj', cupAttachStrandEquiv]

private def cupId (a : List (Letter I)) (n : ℕ) : ℕ :=
  if n < 2 * a.length + 1 then n else n + 1

private theorem cupId_inj (a : List (Letter I)) : Function.Injective (cupId a) := by
  intro x y h
  unfold cupId at h
  split_ifs at h <;> omega

private theorem cupId_zero (a : List (Letter I)) : cupId a 0 = 0 := by simp [cupId]

private theorem idD_map_id (f : ℕ → ℕ) (hf : f 0 = 0)
    (s : List (ℕ × Letter I)) (j : ℕ) :
    idD (s.map (fun z => (f z.1, z.2))) j = f (idD s j) := by
  simp only [idD, idAt_map_fst]
  cases idAt s j <;> simp [hf]

private theorem rlId_map_id (f : ℕ → ℕ) (hf : Function.Injective f) (x y z : ℕ) :
    rlId (f x) (f y) (f z) = f (rlId x y z) := by
  simp only [rlId, hf.eq_iff]
  split_ifs <;> rfl

private theorem jn_map_id (f : ℕ → ℕ) (hf : Function.Injective f)
    (s : List (ℕ × Letter I)) (r : ℕ) :
    jn (s.map (fun z => (f z.1, z.2))) r = (jn s r).map (fun z => (f z.1, z.2)) := by
  simp only [jn, ← List.map_drop]
  cases s.drop r with
  | nil => rfl
  | cons A l =>
    cases l with
    | nil => rfl
    | cons B l =>
      simp only [List.map_cons, ← map_rmAt, List.map_map]
      apply List.map_congr_left
      intro z _
      exact Prod.ext (rlId_map_id f hf B.1 A.1 z.1) rfl

private theorem cupId_step (a : List (Letter I)) (k : ℕ)
    {T U : TState (Letter I)} (hn : 2 * a.length + 1 ≤ T.nxt)
    (hnext : U.nxt = T.nxt + 1)
    (hs : U.st = T.st.map (fun z => (cupId a z.1, z.2))) (m : TMove (Letter I)) :
    2 * a.length + 1 ≤ (tStep flipL k T m).nxt ∧
    (tStep flipL k U m).nxt = (tStep flipL k T m).nxt + 1 ∧
    (tStep flipL k U m).st =
      (tStep flipL k T m).st.map (fun z => (cupId a z.1, z.2)) := by
  rcases m with (⟨g, x⟩ | p) | g
  · refine ⟨by dsimp [tStep]; omega, by simp [tStep, hnext, Nat.add_assoc], ?_⟩
    simp only [tStep, hs, hnext, map_insAt]
    simp [cupId, Nat.not_lt.mpr hn]
  · exact ⟨hn, hnext, by simp only [tStep, hs, map_swapAt]⟩
  · exact ⟨hn, hnext, by simp only [tStep, hs, jn_map_id _ (cupId_inj a)]⟩

private theorem cupId_run (a : List (Letter I)) (k : ℕ) (R : List (TMove (Letter I)))
    {T U : TState (Letter I)} (hn : 2 * a.length + 1 ≤ T.nxt)
    (hnext : U.nxt = T.nxt + 1)
    (hs : U.st = T.st.map (fun z => (cupId a z.1, z.2))) :
    2 * a.length + 1 ≤ (tRun flipL k T R).nxt ∧
    (tRun flipL k U R).nxt = (tRun flipL k T R).nxt + 1 ∧
    (tRun flipL k U R).st =
      (tRun flipL k T R).st.map (fun z => (cupId a z.1, z.2)) := by
  induction R generalizing T U with
  | nil => exact ⟨hn, hnext, hs⟩
  | cons m R ih =>
    obtain ⟨h1, h2, h3⟩ := cupId_step a k hn hnext hs m
    exact ih h1 h2 h3

private theorem cupId_ren (a : List (Letter I)) (k : ℕ) (R : List (TMove (Letter I)))
    {T U : TState (Letter I)} (hn : 2 * a.length + 1 ≤ T.nxt)
    (hnext : U.nxt = T.nxt + 1)
    (hs : U.st = T.st.map (fun z => (cupId a z.1, z.2))) (x : ℕ) :
    tRen k U R (cupId a x) = cupId a (tRen k T R x) := by
  induction R generalizing T U x with
  | nil => rfl
  | cons m R ih =>
    obtain ⟨h1, h2, h3⟩ := cupId_step a k hn hnext hs m
    have he : stepRen k U m (cupId a x) = cupId a (stepRen k T m x) := by
      cases m with
      | mv m => rfl
      | cap g =>
        simp only [stepRen, hs, idD_map_id _ (cupId_zero a)]
        exact rlId_map_id _ (cupId_inj a) _ _ _
    simp only [tRen, he]
    exact ih h1 h2 h3 _

private theorem cupAttach_start_ids (i : I) (a : List (Letter I)) :
    let T := tStep flipL a.length (tStart a) (.mv (.cup 0 (false, i)))
    let U := tStart ((true, i) :: a)
    2 * a.length + 1 ≤ T.nxt ∧ U.nxt = T.nxt + 1 ∧
      U.st = T.st.map (fun z => (cupId a z.1, z.2)) := by
  have hl (l : List (Letter I)) : (run flipL (cupMoves (dualW l))).length = 2 * l.length := by
    rw [run_cupMoves]
    simp only [List.length_append, List.length_map, List.length_reverse, length_cupLeft,
      length_dualW]
    omega
  refine ⟨by simp only [tStep, tStart, hl]; omega,
    by simp only [tStep, tStart, hl, List.length_cons]; omega, ?_⟩
  rw [cupAttach_start_st]
  symm
  conv_rhs => rw [← List.map_id (tStart ((true, i) :: a)).st]
  apply List.map_congr_left
  intro z hz
  have hz' := (tInv_tStart ((true, i) :: a)).fresh z hz
  have hpar : ∃ n, z.1 = 2 * n := by
    simp only [tStart, run_cupMoves, List.mem_append, List.mem_map] at hz
    rcases hz with hz | ⟨y, hy, rfl⟩
    · obtain ⟨n, _, he⟩ := List.mem_mapIdx.mp hz
      exact ⟨n, (congrArg Prod.fst he).symm⟩
    · obtain ⟨n, _, he⟩ := List.mem_mapIdx.mp (List.mem_reverse.mp hy)
      exact ⟨n, (congrArg Prod.fst he).symm⟩
  rcases hpar with ⟨n, hn⟩
  have hlt : z.1 < 2 * a.length + 1 := by
    change z.1 < (run flipL (cupMoves (dualW ((true, i) :: a)))).length at hz'
    rw [hl] at hz'
    simp only [List.length_cons] at hz'
    omega
  simp [cupId, hlt]

private theorem tRen_shift_at (k n : ℕ) (T : TState (Letter I))
    (R : List (TMove (Letter I))) (x : ℕ) :
    tRen k T (R.map (shiftT n)) x = tRen (k + n) T R x := by
  induction R generalizing T x with
  | nil => rfl
  | cons m R ih =>
    simp only [List.map_cons, tRen, tStep_shift_at, ih]
    congr 1
    rcases m with (⟨g, y⟩ | p) | g <;> simp [stepRen, shiftT, Nat.add_assoc]

/-- A bounded distinguished point stays on its original strand after literal attachment.
The proof follows the actual cap renamings, not just the final pairing isomorphism. -/
theorem onStrand₂_cupAttach {i : I} {a b : List (Letter I)}
    {R : List (TMove (Letter I))} (hR : IsMatching₂ ((true, i) :: a) b R)
    {j : ℕ} {p : ℕ × ℕ} (hbound : p.1 ≤ R.length)
    (hp : OnStrand₂ ((true, i) :: a) R j p) :
    (cupAttachPoint p).1 ≤ (cupAttachMatching i R).length ∧
    OnStrand₂ a (cupAttachMatching i R) j (cupAttachPoint p) := by
  let T := tStep flipL a.length (tStart a) (.mv (.cup 0 (false, i)))
  let U := tStart ((true, i) :: a)
  obtain ⟨hn, hnxt, hs⟩ := cupAttach_start_ids i a
  have hrun := cupId_run a (a.length + 1) (R.take p.1) hn hnxt hs
  have hfinal := (cupId_run a (a.length + 1) R hn hnxt hs).2.2
  have htake : TFits flipL (((true, i) :: a).length) U (R.take p.1) := by
    exact ((tFits_append_at _ U (R.take p.1) (R.drop p.1)).1
      (by simpa only [List.take_append_drop] using hR.1)).1
  refine ⟨by simpa [cupAttachPoint, cupAttachMatching] using hbound, ?_, ?_⟩
  · have he := foldl_shift_prefix [(false, i)] (R.take p.1) _ U
      (dualW ((true, i) :: a)) ((true, i) :: a) (length_dualW _) (tStart_letters _) htake
    have hc : tLet a (.mv (.cup 0 (false, i))) = (false, i) :: (true, i) :: a := by
      simpa [tLet, flipL] using chStep_cup ([] : List (Letter I)) a (false, i)
    simp only [List.length_singleton, List.singleton_append] at he
    change p.2 + 1 < (((cupAttachMatching i R).take (p.1 + 1)).foldl tLet a).length
    simp only [cupAttachMatching, List.take_succ_cons, ← List.map_take, List.foldl_cons, hc]
    rw [he, List.length_cons]
    exact Nat.add_lt_add_right hp.1 1
  · have he := hp.2
    change tRen (a.length + 1) (tRun flipL (a.length + 1) U (R.take p.1))
      (R.drop p.1) (idD (tRun flipL (a.length + 1) U (R.take p.1)).st
        (a.length + 1 + p.2)) = idD (tRun flipL (a.length + 1) U R).st j at he
    rw [hfinal, hrun.2.2, idD_map_id _ (cupId_zero a), idD_map_id _ (cupId_zero a),
      cupId_ren a _ _ hrun.1 hrun.2.1 hrun.2.2] at he
    have hc := cupId_inj a he
    simp only [cupAttachPoint, cupAttachMatching, List.take_succ_cons,
      List.drop_succ_cons, ← List.map_take, ← List.map_drop, pairing₂]
    change tRen a.length (tRun flipL a.length T ((R.take p.1).map (shiftT 1)))
      ((R.drop p.1).map (shiftT 1))
      (idD (tRun flipL a.length T ((R.take p.1).map (shiftT 1))).st
        (a.length + (p.2 + 1))) = idD (tRun flipL a.length T (R.map (shiftT 1))).st j
    rw [tRun_shift_at, tRun_shift_at, tRen_shift_at]
    convert hc using 1
    congr 2
    omega

/-- Literal right-cup attachment with bounded distinguished points and finite strand labels.
The ordinary realization remains an explicit input; no normalized representative is chosen. -/
theorem cup_attach_up_decorated {X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {i : I} {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ ((true, i) :: a) b R) :
    IsMatching₂ a ((false, i) :: b) (cupAttachMatching i R) ∧
    Iso (pairing₂ a (cupAttachMatching i R)) (pairing₂ ((true, i) :: a) R) ∧
    ∃ e : MatchingStrand ((true, i) :: a) R ≃ MatchingStrand a (cupAttachMatching i R),
      (∀ j, (e j).val = j.val) ∧
      ∀ (q : ℕ → ℕ × ℕ),
        (∀ j ∈ leftEnds₂ ((true, i) :: a) R,
          (q j).1 ≤ R.length ∧ OnStrand₂ ((true, i) :: a) R j (q j)) →
      ∀ (c : MatchingStrand ((true, i) :: a) R → ℕ) (ds : List (DTMove I)),
        Decorates₂ ((true, i) :: a) R q (strandCounts c) ds →
      ∀ (L : List (LayerData I)) (hL : SChain ((true, i) :: a) L b),
        L.map ofL = dLay ((true, i) :: a) ds →
        (∀ j ∈ leftEnds₂ a (cupAttachMatching i R),
          (cupAttachPoint (q j)).1 ≤ (cupAttachMatching i R).length ∧
            OnStrand₂ a (cupAttachMatching i R) j (cupAttachPoint (q j))) ∧
        Decorates₂ a (cupAttachMatching i R) (cupAttachPoint ∘ q)
          (strandCounts (c ∘ e.symm)) (cupAttachMoves i ds) ∧
        ∃ hLB : SChain a (cupAttachLayers i a L) ((false, i) :: b),
          (cupAttachLayers i a L).map ofL = dLay a (cupAttachMoves i ds) ∧
          Diagram.degree (gdeg D sy) (mkD D μ (cupAttachLayers i a L) hLB) =
            Diagram.degree (gdeg D sy) (mkD D μ L hL) +
              sy.d i * (1 + D.h i (wt D μ a)) ∧
          xpar D μ (dLay a (cupAttachMoves i ds)) =
            xpar D μ (dLay ((true, i) :: a) ds) := by
  obtain ⟨hm, hi⟩ := cupAttach_matching_iso hR
  refine ⟨hm, hi, cupAttachStrandEquiv hR, fun _ => rfl, ?_⟩
  intro q hq c ds hd L hL he
  refine ⟨?_, decorates₂_cupAttach hR q c hd,
    cup_attach_up_degree_parity D sy μ hR hd.1 L hL he⟩
  intro j hj
  rw [leftEnds₂_cupAttach hR] at hj
  exact onStrand₂_cupAttach hR (hq j hj).1 (hq j hj).2

end OddMath.SKM
