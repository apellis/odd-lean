import OddMath.SKM.PositiveMatchings

/-!
# Crossing layers of positive strictly reduced matchings

The crossing-only reduction underlying [BE2, arXiv:1701.04133v2, Theorem 10.3,
proof of Claim 1], with reducedness as in §8. Critical-point records rule out caps;
endpoint length then rules out cups. The resulting ordinary layers map to the existing
`tLay`, with the same endpoints. No weighted degree, parity or graphical series formula
is asserted here.
-/

namespace OddMath.SKM
open StringDiagrams.Chord
variable {I : Type*}

private theorem crit_nodup_input {k : ℕ} {T : TState (Letter I)} {cl : List ℕ}
    (R : List (TMove (Letter I))) (h : (tCrit flipL k T cl R).Nodup) : cl.Nodup := by
  induction R generalizing T cl with
  | nil => exact h
  | cons m R ih =>
    have h' := ih h
    cases m with
    | mv m => cases m with
      | cup g a => exact (List.nodup_append.mp h').1
      | cross p => exact h'
    | cap g => exact List.Nodup.of_map _ (List.nodup_append.mp h').1

-- Downward active strands have already encountered a cup. Bent endpoints are excluded.
private def DownRecorded (k : ℕ) (T : TState (Letter I)) (cl : List ℕ) : Prop :=
  ∀ p e, k ≤ p → T.st[p]? = some e → e.2.1 = false → e.1 ∈ cl

private theorem down_cup {k : ℕ} {T : TState (Letter I)} {cl : List ℕ}
    (h : DownRecorded k T cl) {g : ℕ} {a : Letter I} (hg : k + g ≤ T.st.length) :
    DownRecorded k (tStep flipL k T (.mv (.cup g a))) (cl ++ [T.nxt]) := by
  intro p e hp he hd
  change (insAt T.st (k + g) (T.nxt, a) (T.nxt, flipL a))[p]? = some e at he
  rw [getElem?_insAt _ hg] at he
  split_ifs at he with h₁ h₂ h₃
  · exact List.mem_append_left _ (h p e hp he hd)
  · cases Option.some.inj he; simp
  · cases Option.some.inj he; simp
  · exact List.mem_append_left _ (h (p - 2) e (by omega) he hd)

private theorem down_cross {k : ℕ} {T : TState (Letter I)} {cl : List ℕ}
    (h : DownRecorded k T cl) {p : ℕ} (hp : k + p + 1 < T.st.length) :
    DownRecorded k (tStep flipL k T (.mv (.cross p))) cl := by
  intro q e hq he hd
  change (swapAt T.st (k + p))[q]? = some e at he
  rw [getElem?_swapAt _ hp] at he
  exact h (tau (k + p) q) e (by unfold tau; split_ifs <;> omega) he hd

-- A first cap repeats a critical-point record, irrespective of subsequent renamings.
private theorem no_caps {k : ℕ} {T : TState (Letter I)} {cl : List ℕ}
    (R : List (TMove (Letter I))) (hf : TFits flipL k T R)
    (hd : DownRecorded k T cl) (hn : (tCrit flipL k T cl R).Nodup) :
    ∀ g, TMove.cap g ∉ R := by
  induction R generalizing T cl with
  | nil => simp
  | cons m R ih =>
    obtain ⟨hm, hf⟩ := hf
    have hn' := crit_nodup_input R hn
    cases m with
    | mv m =>
      cases m with
      | cup g a =>
        have hi := ih hf (down_cup hd hm) hn
        simpa using hi
      | cross p =>
        have hi := ih hf (down_cross hd hm) hn
        simpa using hi
    | cap g =>
      obtain ⟨A, B, hA, hB, hAB, _⟩ := hm
      have eA : idD T.st (k + g) = A.1 := by simp [idD, idAt, hA]
      have eB : idD T.st (k + g + 1) = B.1 := by simp [idD, idAt, hB]
      change (cl.map (rlId (idD T.st (k + g + 1)) (idD T.st (k + g))) ++
        [idD T.st (k + g)]).Nodup at hn'
      rw [eA, eB] at hn'
      have hmem : A.1 ∈ cl.map (rlId B.1 A.1) := by
        cases hb : B.2.1 with
        | false => exact List.mem_map.mpr ⟨B.1, hd _ B (by omega) hB hb, by simp [rlId]⟩
        | true =>
          have ha : A.2.1 = false := by rw [hAB]; simp [flipL, hb]
          exact List.mem_map.mpr ⟨A.1, hd _ A (by omega) hA ha, by simp [rlId]⟩
      exact False.elim ((List.nodup_append.mp hn').2.2 _ hmem _ (by simp) rfl)

private theorem crossing_of_length {k : ℕ} {T : TState (Letter I)}
    (R : List (TMove (Letter I))) (hf : TFits flipL k T R)
    (hc : ∀ g, TMove.cap g ∉ R) :
    T.st.length ≤ (tRun flipL k T R).st.length ∧
    ((tRun flipL k T R).st.length ≤ T.st.length →
      ∀ m ∈ R, ∃ p, m = TMove.mv (Move.cross p)) := by
  induction R generalizing T with
  | nil => exact ⟨le_rfl, by simp⟩
  | cons m R ih =>
    obtain ⟨hm, hf⟩ := hf
    have hc' : ∀ g, TMove.cap g ∉ R := fun g hg => hc g (List.mem_cons_of_mem _ hg)
    obtain ⟨hlen, hi⟩ := ih hf hc'
    cases m with
    | cap g => exact False.elim (hc g List.mem_cons_self)
    | mv m => cases m with
      | cup g a =>
        have he : (tStep flipL k T (.mv (.cup g a))).st.length = T.st.length + 2 :=
          length_insAt _ hm _ _
        change T.st.length ≤ (tRun flipL k (tStep flipL k T (.mv (.cup g a))) R).st.length ∧ _
        constructor
        · omega
        · intro h; change (tRun flipL k (tStep flipL k T (.mv (.cup g a))) R).st.length ≤ _ at h
          omega
      | cross p =>
        have he : (tStep flipL k T (.mv (.cross p))).st.length = T.st.length := length_swapAt _ _
        refine ⟨by simpa [tRun, List.foldl_cons, he] using hlen, ?_⟩
        intro h m hm'
        rcases List.mem_cons.mp hm' with rfl | hm'
        · exact ⟨p, rfl⟩
        · exact hi (by simpa [tRun, List.foldl_cons, he] using h) m hm'

/-- A positive strictly reduced matching has only crossings. This is the layering reduction
used in [BE2, arXiv:1701.04133v2, Theorem 10.3, proof of Claim 1], with the §8
critical-point condition. Neither finiteness of the colour type nor distinct colours is needed. -/
theorem IsMatching₂.positive_crossing_moves {c d : ℕ} (a : Fin c → I) (b : Fin d → I)
    {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun s => (true, b s)) R)
    (hred : StrictReduced₂ (List.ofFn fun r => (true, a r)) R) :
    ∀ m ∈ R, ∃ p : ℕ, m = TMove.mv (Move.cross p) := by
  let A := List.ofFn fun r => (true, a r)
  have hd : DownRecorded A.length (tStart A) [] := by
    intro p e hp he hdown
    have hh : ((tStart A).st.map Prod.snd)[p]? = some e.2 := by
      rw [List.getElem?_map, he]; rfl
    rw [tStart_letters, List.getElem?_append_right (by simpa [length_dualW] using hp)] at hh
    have hm := List.mem_of_getElem? hh
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
    have := congrArg Prod.fst hi
    simp [hdown] at this
  have hc := no_caps R hR.1 hd hred.2
  apply (crossing_of_length R hR.1 hc).2
  have hs := congrArg List.length (tStart_letters A)
  have ht := congrArg List.length
    (letters_tRun (length_dualW A) R (tStart A) A (tStart_letters A) hR.1)
  rw [hR.2] at ht
  have he := hR.positive_length_eq a b
  simp only [List.length_map, List.length_append, length_dualW] at hs ht
  simp only [A, List.length_ofFn] at hs ht ⊢
  omega

private theorem crossing_layers {k : ℕ} {u : List (Letter I)} (hu : u.length = k)
    (R : List (TMove (Letter I))) (T : TState (Letter I)) (l : List (Letter I))
    (hl : T.st.map Prod.snd = u ++ l) (hf : TFits flipL k T R)
    (hp : ∀ x ∈ l, x.1 = true) (hc : ∀ m ∈ R, ∃ p, m = TMove.mv (Move.cross p)) :
    ∃ L : List (LayerData I), SChain l L (R.foldl tLet l) ∧
      L.map ofL = tLay l R ∧ ∀ x ∈ L, ∃ i j, x.2.1 = Shape.cross i j := by
  induction R generalizing T l with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons m R ih =>
    obtain ⟨p, rfl⟩ := hc m List.mem_cons_self
    obtain ⟨hm, hf⟩ := hf
    have hlen : T.st.length = k + l.length := by
      have h := congrArg List.length hl
      simpa [hu] using h
    have hpos : p + 1 < l.length := by change k + p + 1 < T.st.length at hm; omega
    have hnext := letters_tRun hu [TMove.mv (Move.cross p)] T l hl ⟨hm, trivial⟩
    simp only [tRun, List.foldl_cons, List.foldl_nil] at hnext
    obtain ⟨v, x, y, w, rfl, rfl⟩ := exists_split_cross hpos
    have hx := hp x (by simp)
    have hy := hp y (by simp)
    obtain ⟨sx, i⟩ := x
    obtain ⟨sy, j⟩ := y
    dsimp only at hx hy
    subst sx sy
    have hstep : tLet (v ++ (true, i) :: (true, j) :: w) (.mv (.cross v.length)) =
        v ++ (true, j) :: (true, i) :: w := chStep_cross v w _ _
    rw [hstep] at hnext
    obtain ⟨L, hL, he, hsh⟩ := ih _ _ hnext hf
      (by simpa only [List.mem_append, List.mem_cons, or_left_comm, or_assoc] using hp)
      (fun m hm => hc m (List.mem_cons_of_mem _ hm))
    refine ⟨(v, Shape.cross i j, w) :: L, ?_, ?_, ?_⟩
    · simp only [List.foldl_cons, hstep, sChain_cons, Shape.dom, Shape.cod,
        List.append_assoc, List.cons_append, List.nil_append]
      exact ⟨trivial, hL⟩
    · simp only [List.map_cons, tLay, tmLay, moveLay_cross, hstep, ← he]
      simp [show (true, i) = up i from rfl, show (true, j) = up j from rfl,
        xCrL_up_up, xwhL, ofL]
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨i, j, rfl⟩
      · exact hsh z hz

/-- Extract ordinary upward-crossing layers from the existing extended layers of a positive
strictly reduced matching. This supports the diagrammatic computation in [BE2,
arXiv:1701.04133v2, Theorem 10.3, proof of Claim 1]; it does not compute degree or parity. -/
theorem positive_tLay_ofL {c d : ℕ} (a : Fin c → I) (b : Fin d → I)
    {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun s => (true, b s)) R)
    (hred : StrictReduced₂ (List.ofFn fun r => (true, a r)) R) :
    ∃ L : List (LayerData I),
      SChain (List.ofFn fun r => (true, a r)) L (List.ofFn fun s => (true, b s)) ∧
      L.map ofL = tLay (List.ofFn fun r => (true, a r)) R ∧
      ∀ x ∈ L, ∃ i j, x.2.1 = Shape.cross i j := by
  obtain ⟨L, hL, he, hsh⟩ := crossing_layers (length_dualW _) R _ _ (tStart_letters _) hR.1
    (by intro x hx; obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hx; rfl)
    (hR.positive_crossing_moves a b hred)
  exact ⟨L, hR.2 ▸ hL, he, hsh⟩

end OddMath.SKM
