import OddMath.SKM.PositiveMatchingDots

/-! # Strand colours through mixed matchings

The geometric dot-colour input for BE2 v2 §8 and Theorem 10.3.
Colours are transported through the full state run, including cap renaming.
-/

namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord

private def Colours {I : Type*} (T : TState (Letter I)) (c : ℕ → Option I) : Prop :=
  ∀ e ∈ T.st, c e.1 = some e.2.2

private theorem colours_step {I : Type*} {T : TState (Letter I)} (hv : TInv T)
    {c : ℕ → Option I} (hc : Colours T c) {k : ℕ} {m : TMove (Letter I)}
    (hm : m.Ok flipL k T.st) :
    ∃ c', Colours (tStep flipL k T m) c' ∧
      ∀ x < T.nxt, stepRen k T m x < (tStep flipL k T m).nxt ∧
        c' (stepRen k T m x) = c x := by
  classical
  rcases m with (⟨g, a⟩ | p) | g
  · refine ⟨Function.update c T.nxt (some a.2), ?_, ?_⟩
    · intro e he
      rcases mem_insAt he with he | rfl | rfl
      · simpa [Function.update_of_ne (hv.fresh e he).ne] using hc e he
      · simp
      · simp [flipL]
    · intro x hx
      simp [stepRen, tStep, Function.update_of_ne hx.ne]
      omega
  · refine ⟨c, ?_, ?_⟩
    · intro e he
      obtain ⟨u, a, b, v, hs, hp⟩ := exists_split_cross hm
      change e ∈ swapAt T.st (k + p) at he
      rw [← hp, hs, swapAt_mid] at he
      apply hc
      rw [hs]
      simpa only [List.mem_append, List.mem_cons, or_left_comm, or_assoc] using he
    · intro x hx
      exact ⟨hx, rfl⟩
  · obtain ⟨a, b, ha, hb, hab, _⟩ := hm
    have ha' := List.mem_of_getElem? ha
    have hb' := List.mem_of_getElem? hb
    have hr : k + g + 1 < T.st.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hb
      cases hb
    have ea : idD T.st (k + g) = a.1 := by simp [idD, idAt, ha]
    have eb : idD T.st (k + g + 1) = b.1 := by simp [idD, idAt, hb]
    have ec : c a.1 = c b.1 := by rw [hc a ha', hc b hb', hab]; rfl
    have er (x : ℕ) : c (rlId b.1 a.1 x) = c x := by
      simp only [rlId]
      split_ifs with h
      · simpa [h] using ec
      · rfl
    refine ⟨c, ?_, ?_⟩
    · intro e he
      obtain ⟨e', he', rfl⟩ := mem_jn hr he
      simp only [rl, ea, eb]
      exact (er e'.1).trans (hc e' he')
    · intro x hx
      simp only [stepRen, tStep, ea, eb]
      refine ⟨?_, er x⟩
      unfold rlId
      split_ifs
      · exact hv.fresh a ha'
      · exact hx

private theorem colours_run {I : Type*} {k : ℕ} (R : List (TMove (Letter I)))
    {T : TState (Letter I)} (hv : TInv T) {c : ℕ → Option I} (hc : Colours T c)
    (hf : TFits flipL k T R) :
    ∃ c', Colours (tRun flipL k T R) c' ∧
      ∀ x < T.nxt, c' (tRen k T R x) = c x := by
  induction R generalizing T c with
  | nil => exact ⟨c, hc, fun _ _ => rfl⟩
  | cons m R ih =>
    obtain ⟨c', hc', ht⟩ := colours_step hv hc hf.1
    obtain ⟨c'', hc'', hr⟩ := ih (hv.step hf.1) hc' hf.2
    refine ⟨c'', hc'', fun x hx => ?_⟩
    exact (hr _ (ht x hx).1).trans (ht x hx).2

private theorem colours_start {I : Type*} (a : List (Letter I)) :
    Colours (tStart a) (fun n => ((dualW a)[n / 2]?).map Prod.snd) := by
  have left {e : ℕ × Letter I} (he : e ∈ cupLeft (dualW a)) :
      ((dualW a)[e.1 / 2]?).map Prod.snd = some e.2.2 := by
    obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp he
    simp [List.getElem?_eq_getElem hi]
  intro e he
  simp only [tStart, run_cupMoves, List.mem_append] at he
  rcases he with he | he
  · exact left he
  · change e ∈ (cupLeft (dualW a)).reverse.map flipSnd at he
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp he
    exact left (e := z) (List.mem_reverse.mp hz)

private theorem fits_split {I : Type*} (k : ℕ) (T : TState (Letter I))
    (R : List (TMove (Letter I))) (hf : TFits flipL k T R) (n : ℕ) :
    TFits flipL k T (R.take n) ∧
      TFits flipL k (tRun flipL k T (R.take n)) (R.drop n) := by
  induction R generalizing T n with
  | nil => simp [TFits]
  | cons m R ih =>
    cases n with
    | zero => exact ⟨trivial, hf⟩
    | succ n =>
      obtain ⟨h1, h2⟩ := ih _ hf.2 n
      exact ⟨⟨hf.1, h1⟩, h2⟩

/-- Colour of a strand, read at its existing left endpoint in the final pairing. -/
def matchingStrandColour {I : Type*} (a : List (Letter I)) (R : List (TMove (Letter I)))
    (j : MatchingStrand a R) : I :=
  ((pairing₂ a R)[j.val]'(mem_leftEnds₂.mp j.property).1).2.2

/-- A point on any mixed matching has the colour of its strand's left endpoint.
No reducedness, finiteness of the colour type, or Cartan-data assumptions are needed.
The run and renaming use the existing cups, crossings and caps. -/
theorem onStrand₂_colour {I : Type*} {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a b R) (j : MatchingStrand a R) {q : ℕ × ℕ}
    (hq : OnStrand₂ a R j q) :
    (((R.take q.1).foldl tLet a)[q.2]?).map Prod.snd =
      some (matchingStrandColour a R j) := by
  let T := tRun flipL a.length (tStart a) (R.take q.1)
  obtain ⟨hf, hs⟩ := fits_split a.length (tStart a) R hR.1 q.1
  obtain ⟨c, hc, _⟩ := colours_run (R.take q.1) (tInv_tStart a) (colours_start a) hf
  obtain ⟨d, hd, he⟩ := colours_run (R.drop q.1) ((tInv_tStart a).run hf) hc hs
  have hr : tRun flipL a.length T (R.drop q.1) = tRun flipL a.length (tStart a) R := by
    change (R.drop q.1).foldl (tStep flipL a.length)
      ((R.take q.1).foldl (tStep flipL a.length) (tStart a)) = _
    rw [← List.foldl_append, List.take_append_drop]
    rfl
  rw [hr] at hd
  have hl := letters_tRun (length_dualW a) (R.take q.1) (tStart a) a (tStart_letters a) hf
  have hlen : T.st.length = a.length + ((R.take q.1).foldl tLet a).length := by
    have hh := congrArg List.length hl
    simpa [T, length_dualW] using hh
  have hp : a.length + q.2 < T.st.length := by have := hq.1; omega
  let x := T.st[a.length + q.2]
  have hx : T.st[a.length + q.2]? = some x := List.getElem?_eq_getElem hp
  have hxlet : ((R.take q.1).foldl tLet a)[q.2]? = some x.2 := by
    have hh := congrArg (fun l => l[a.length + q.2]?) hl
    rw [List.getElem?_map, hx] at hh
    simpa [List.getElem?_append_right, length_dualW] using hh.symm
  have hxi : idD T.st (a.length + q.2) = x.1 := by simp [idD, idAt, hx]
  have hj : j.val < (pairing₂ a R).length := (mem_leftEnds₂.mp j.property).1
  let y := (pairing₂ a R)[j.val]
  have hy : (pairing₂ a R)[j.val]? = some y := List.getElem?_eq_getElem hj
  have hyi : idD (pairing₂ a R) j.val = y.1 := by simp [idD, idAt, hy]
  have hxy : tRen a.length T (R.drop q.1) x.1 = y.1 := by
    simpa only [← hxi, ← hyi] using hq.2
  have hmem := List.mem_of_getElem? hx
  have hxcol := (he x.1 (((tInv_tStart a).run hf).fresh x hmem)).trans (hc x hmem)
  rw [hxy, hd y (List.mem_of_getElem? hy)] at hxcol
  rw [hxlet]
  exact hxcol.symm

end OddMath.SKM
