/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChordTwoSided
import OddMath.SKM.SpanCapTrack
import OddMath.SKM.SpanBend

/-!
# Reduced two-sided matchings

Towards J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 8.1
for a general bottom boundary `a`. The paper omits the proof, referring to M. Khovanov,
A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11.

An `(a, b)`-matching is encoded by a generic layering `R : List (Chord.TMove (Letter I))` of cups,
crossings and caps (`IsMatching₂`), with layers `tLay a R` from `E_a 1_μ` to `E_b 1_μ`. Bending
the bottom boundary up by the nested cups `cupA a*` (as in `OddMath.SKM.SpanBend`), the matching is
followed by a one-sided chord diagram: cups and crossings are copied, and each cap is removed by
the cap push of `OddMath.SKM.SpanCapTrack` (`tProcess`). The crossings of a matching are tracked
on the strands of the bent picture (`Chord.TState`); a matching is *reduced* (`Reduced₂`) if no
strand crosses itself and two strands cross at most once ([BE2] §8). By the parity bound
`Chord.length_xs_le_cr`, the one-sided diagram of a reduced matching is reduced, hence equivalent
to the canonical diagram of its pairing.

## Main results

* `tProcess`: a matching on top of a one-sided diagram is, up to sign modulo fewer crossings, a
  one-sided diagram with the joined pairing and at most as many crossings.
* `reduced₂_normal_form`: **a reduced `(a, b)`-matching has as many crossings as its pairing, and
  agrees up to sign, modulo diagrams with fewer crossings, with the canonical chord diagram of its
  pairing bent back by nested caps (`bendL`)**.

The paper's notion of reduced matchings also asks that every strand has at most one critical
point; this is not needed here, so `Reduced₂` admits more matchings.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation
open StringDiagrams.Chord (Move Fits run Iso rl rlId TMove TState tStep tRun TFits TInv ncr₂ jn
  canon)

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} {cs : CScalars Sc}

/-! ## Shifted chord diagrams -/

/-- A move shifted `n` positions to the right. -/
def shiftM (n : ℕ) : Move (Letter I) → Move (Letter I)
  | .cup g a => .cup (n + g) a
  | .cross p => .cross (n + p)

theorem moveLay_shift (u v : List (Letter I)) {l : List (Letter I)} {m : Move (Letter I)}
    (hm : m.Ok l.length) :
    moveLay (u ++ l ++ v) (shiftM u.length m) = (moveLay l m).map (xwhL u v) ∧
      chStep (u ++ l ++ v) (shiftM u.length m) = u ++ chStep l m ++ v := by
  cases m with
  | cup g a =>
    obtain ⟨x, w, rfl, rfl⟩ := exists_split_cup (l := l) (g := g) hm
    have e : u ++ (x ++ w) ++ v = (u ++ x) ++ (w ++ v) := by simp
    have e2 : u.length + x.length = (u ++ x).length := by simp
    simp only [shiftM]
    rw [e, e2, moveLay_cup, chStep_cup, moveLay_cup, chStep_cup, map_xwhL_xwhL]
    simp
  | cross p =>
    obtain ⟨x, a, b, w, rfl, rfl⟩ := exists_split_cross (l := l) (p := p) hm
    have e : u ++ (x ++ a :: b :: w) ++ v = (u ++ x) ++ a :: b :: (w ++ v) := by simp
    have e2 : u.length + x.length = (u ++ x).length := by simp
    simp only [shiftM]
    rw [e, e2, moveLay_cross, chStep_cross, moveLay_cross, chStep_cross, map_xwhL_xwhL]
    simp

theorem chordLay_shift (u v : List (Letter I)) : ∀ {l : List (Letter I)}
    {E : List (Move (Letter I))}, Fits l.length E →
    chordLay (u ++ l ++ v) (E.map (shiftM u.length)) = (chordLay l E).map (xwhL u v) ∧
      (E.map (shiftM u.length)).foldl chStep (u ++ l ++ v) = u ++ E.foldl chStep l ++ v
  | _, [], _ => by simp [chordLay]
  | l, m :: E, h => by
    obtain ⟨h1, h2⟩ := moveLay_shift u v h.1
    obtain ⟨h3, h4⟩ := chordLay_shift u v (fits_chStep h)
    simp only [List.map_cons, chordLay, List.foldl_cons, h1, h2, h3, h4, List.map_append, and_self]

theorem fits_shift (a b : ℕ) : ∀ {n : ℕ} {E : List (Move (Letter I))}, Fits n E →
    ∀ N, N = a + n + b → Fits N (E.map (shiftM a))
  | _, [], _, _, _ => trivial
  | n, m :: E, h, N, hN => by
    cases m with
    | cup g x =>
      exact ⟨show a + g ≤ N by have := h.1; simp only [Move.Ok] at this; omega,
        fits_shift a b h.2 _ (by simp only [Move.len, shiftM]; omega)⟩
    | cross p =>
      exact ⟨show a + p + 1 < N by have := h.1; simp only [Move.Ok] at this; omega,
        fits_shift a b h.2 _ (by simp only [Move.len, shiftM]; omega)⟩

theorem ncr_shift (a : ℕ) : ∀ E : List (Move (Letter I)), ncr (E.map (shiftM a)) = ncr E
  | [] => rfl
  | m :: E => by cases m <;> simp [shiftM, ncr_shift a E]

/-- The nested cups `cupA w` as a chord diagram. -/
def cupMoves : List (Letter I) → List (Move (Letter I))
  | [] => []
  | x :: w => .cup 0 x :: (cupMoves w).map (shiftM 1)

theorem cupMoves_spec : ∀ w : List (Letter I),
    Fits 0 (cupMoves w) ∧ ncr (cupMoves w) = 0 ∧ chordLay [] (cupMoves w) = cupA w ∧
      (cupMoves w).foldl chStep [] = w ++ dualW w
  | [] => ⟨trivial, by simp [cupMoves, chordLay]⟩
  | x :: w => by
    obtain ⟨h1, h2, h3, h4⟩ := cupMoves_spec w
    obtain ⟨h5, h6⟩ := chordLay_shift [x] [flipL x] (l := []) h1
    rw [show ([x] : List (Letter I)).length = 1 from rfl] at h5 h6
    have e : chStep [] (.cup 0 x) = [x] ++ [] ++ [flipL x] := by
      simpa using chStep_cup ([] : List (Letter I)) [] x
    refine ⟨⟨by simp [Move.Ok], fits_shift 1 1 h1 _ rfl⟩, ?_, ?_, ?_⟩
    · simp [cupMoves, ncr_shift, h2]
    · simp only [cupMoves, chordLay, e]
      rw [h5, h3, cupA]
      simpa using moveLay_cup ([] : List (Letter I)) [] x
    · simp only [cupMoves, List.foldl_cons, e]
      rw [h6, h4]; simp

/-! ## The layers of a two-sided matching -/

/-- The layers of a move of a two-sided matching applied to the letters `l`. -/
def tmLay (l : List (Letter I)) : TMove (Letter I) → List (XLayer I)
  | .mv m => moveLay l m
  | .cap g => match l.drop g with
    | _ :: y :: w => (xCapL y).map (xwhL (l.take g) w)
    | _ => []

/-- The letters after a move of a two-sided matching. -/
def tLet (l : List (Letter I)) : TMove (Letter I) → List (Letter I)
  | .mv m => chStep l m
  | .cap g => l.take g ++ l.drop (g + 2)

/-- **The layers of a two-sided matching** (moves read from the bottom) starting from the
letters `l`. -/
def tLay : List (Letter I) → List (TMove (Letter I)) → List (XLayer I)
  | _, [] => []
  | l, m :: R => tmLay l m ++ tLay (tLet l m) R

theorem tmLay_cap (v w : List (Letter I)) (x y : Letter I) :
    tmLay (v ++ x :: y :: w) (.cap v.length) = (xCapL y).map (xwhL v w) ∧
      tLet (v ++ x :: y :: w) (.cap v.length) = v ++ w := by
  simp [tmLay, tLet]

/-- **An `(a, b)`-matching** in the bent picture: every move applies, starting from the nested
cups bending `a` up to the left, and the top letters are `b`. -/
def tStart (a : List (Letter I)) : TState (Letter I) :=
  ⟨(run flipL (cupMoves (dualW a))).length, run flipL (cupMoves (dualW a)), []⟩

/-- **`(a, b)`-matchings**, as generic layerings of cups, crossings and caps. -/
def IsMatching₂ (a b : List (Letter I)) (R : List (TMove (Letter I))) : Prop :=
  TFits flipL a.length (tStart a) R ∧ R.foldl tLet a = b

/-- The pairing of a two-sided matching, on the letters `a* b`. -/
def pairing₂ (a : List (Letter I)) (R : List (TMove (Letter I))) : List (ℕ × Letter I) :=
  (tRun flipL a.length (tStart a) R).st

/-- **Reduced matchings** ([BE2] §8): no strand crosses itself and two strands cross at most
once (the crossings being recorded on the strands of the matching, `Chord.TState.xs`). -/
def Reduced₂ (a : List (Letter I)) (R : List (TMove (Letter I))) : Prop :=
  (tRun flipL a.length (tStart a) R).xs.Nodup ∧
    ∀ z ∈ (tRun flipL a.length (tStart a) R).xs, ¬ z.IsDiag

/-! ## Following a matching by a one-sided diagram -/

theorem split_state {T : List (ℕ × Letter I)} {u l : List (Letter I)}
    (hl : T.map Prod.snd = u ++ l) {p : ℕ} (hp : p + 1 < l.length) :
    ∃ U X Y W v x y w, T = U ++ X :: Y :: W ∧ U.length = u.length + p ∧
      l = v ++ x :: y :: w ∧ v.length = p ∧ X.2 = x ∧ Y.2 = y ∧ U.map Prod.snd = u ++ v ∧
      W.map Prod.snd = w := by
  obtain ⟨v, x, y, w, rfl, rfl⟩ := exists_split_cross hp
  have hT : u.length + v.length + 1 < T.length := by
    have := congrArg List.length hl; simp at this; omega
  obtain ⟨U, X, Y, W, rfl, hU⟩ := exists_split_cross hT
  refine ⟨U, X, Y, W, v, x, y, w, rfl, hU, rfl, rfl, ?_⟩
  simp only [List.map_append, List.map_cons] at hl
  rw [← List.append_assoc] at hl
  obtain ⟨h1, h2⟩ := List.append_inj hl (by simp [hU])
  simp only [List.cons.injEq] at h2
  exact ⟨h2.1, h2.2.1, h1, h2.2.2⟩

theorem lettered_of_iso {s s' : List (ℕ × Letter I)} (h : Iso s s')
    (hl : Chord.Lettered flipL s) : Chord.Lettered flipL s' := by
  intro i j hs hij
  have e : ∀ n, (s'[n]?).map Prod.snd = (s[n]?).map Prod.snd := fun n => by
    rw [← List.getElem?_map, ← List.getElem?_map, h.1]
  rw [e j, hl i j ((h.2 i j).2 hs) hij, ← Option.map_map, ← Option.map_map, e i]

theorem ncr₂_cons (m : TMove (Letter I)) (R : List (TMove (Letter I))) :
    ncr₂ (m :: R) = ncr₂ [m] + ncr₂ R := by
  rw [show m :: R = [m] ++ R from rfl, ncr₂, List.countP_append, ← ncr₂, ← ncr₂]

variable (cs)

/-- **One move of a matching on top of a one-sided diagram.** -/
theorem tPush (μ : X) {k : ℕ} {T : TState (Letter I)} (I₀ : TInv T)
    {E : List (Move (Letter I))} (hf : Fits 0 E) (hiso : Iso (run flipL E) T.st)
    {u l : List (Letter I)} (hu : u.length = k) (hl : T.st.map Prod.snd = u ++ l)
    {m : TMove (Letter I)} (hm : m.Ok flipL k T.st) :
    (tStep flipL k T m).st.map Prod.snd = u ++ tLet l m ∧ XChain l (tmLay l m) (tLet l m) ∧
      xcnt (tmLay l m) = ncr₂ [m] ∧
      ∃ E', Fits 0 E' ∧ Iso (run flipL E') (tStep flipL k T m).st ∧
        ncr E' ≤ ncr E + ncr₂ [m] ∧
        (ncr E' = ncr E + ncr₂ [m] → XLt cs μ [] (u ++ tLet l m) (ncr E + ncr₂ [m])
          (chordLay [] E ++ (tmLay l m).map (xwhL u [])) (chordLay [] E')) := by
  have hlen : T.st.length = u.length + l.length := by
    have := congrArg List.length hl; simpa using this
  have hrun : (run flipL E).map Prod.snd = u ++ l := by rw [hiso.1, hl]
  have hchE : XChain [] (chordLay [] E) (u ++ l) := by rw [← hrun]; exact xChain_run hf
  rcases m with (⟨g, a⟩ | p) | g
  · -- a cup
    simp only [TMove.Ok] at hm
    have hg : g ≤ l.length := by omega
    have hok : (Move.cup g a).Ok l.length := hg
    obtain ⟨hlay, hstep⟩ := moveLay_shift u [] hok
    simp only [List.append_nil] at hlay hstep
    rw [hu] at hlay hstep
    simp only [shiftM] at hlay hstep
    have hm' : (Move.cup (k + g) a).Ok (run flipL E).length := by
      show k + g ≤ _; rw [hiso.length_eq]; exact hm
    refine ⟨?_, xChain_moveLay hok, by rw [tmLay, xcnt_moveLay hok]; rfl,
      E ++ [.cup (k + g) a], fits_snoc'.2 ⟨hf, hm'⟩, ?_, ?_, fun _ => ?_⟩
    · obtain ⟨v, w, rfl, rfl⟩ := exists_split_cup hg
      obtain ⟨U, W, hT, hU⟩ := exists_split_cup (l := T.st) (g := k + v.length) hm
      rw [hT] at hl
      simp only [List.map_append] at hl
      obtain ⟨h1, h2⟩ := List.append_inj (s₁ := U.map Prod.snd) (t₁ := W.map Prod.snd)
        (s₂ := u ++ v) (t₂ := w) (by simpa using hl) (by simp [hU, hu])
      simp only [tStep, tLet, chStep_cup, hT]
      rw [← hU]
      simp [Chord.insAt, h1, h2]
    · rw [run_snoc]
      exact hiso.insAt hm' (fun x hx => ((Chord.inv_run (d := flipL) hf).2 x hx).ne)
        (fun x hx => (I₀.fresh x hx).ne) a (flipL a)
    · simp [ncr_append, ncr₂]
    · refine XLt.congr ?_ rfl (XLt.refl _)
      rw [chordLay_snoc, hrun, hlay]; rfl
  · -- a crossing
    simp only [TMove.Ok] at hm
    have hp : p + 1 < l.length := by omega
    have hok : (Move.cross (α := Letter I) p).Ok l.length := hp
    obtain ⟨hlay, hstep⟩ := moveLay_shift u [] hok
    simp only [List.append_nil] at hlay hstep
    rw [hu] at hlay hstep
    simp only [shiftM] at hlay hstep
    have hm' : (Move.cross (α := Letter I) (k + p)).Ok (run flipL E).length := by
      show k + p + 1 < _; rw [hiso.length_eq]; exact hm
    refine ⟨?_, xChain_moveLay hok, by rw [tmLay, xcnt_moveLay hok]; rfl,
      E ++ [.cross (k + p)], fits_snoc'.2 ⟨hf, hm'⟩, ?_, ?_, fun _ => ?_⟩
    · obtain ⟨U, X, Y, W, v, x, y, w, hT, hU, rfl, rfl, hX, hY, h1, h2⟩ := split_state hl hp
      simp only [tStep, tLet, hT, chStep_cross]
      rw [← hu, ← hU, swapAt_mid]
      simp [h1, h2, hX, hY]
    · rw [run_snoc]
      exact hiso.swapAt (k + p)
    · simp [ncr_append, ncr₂]
    · refine XLt.congr ?_ rfl (XLt.refl _)
      rw [chordLay_snoc, hrun, hlay]; rfl
  · -- a cap
    obtain ⟨A, B, hA, hB, hAB, hne⟩ := hm
    have hr : k + g + 1 < T.st.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hB; cases hB
    have hg : g + 1 < l.length := by omega
    obtain ⟨U, X, Y, W, v, x, y, w, hT, hU, rfl, rfl, hX, hY, h1, h2⟩ := split_state hl hg
    have hXA : X = A := by
      rw [hT, show k + v.length = U.length by omega] at hA; simpa using hA
    have hYB : Y = B := by
      rw [hT, show k + v.length + 1 = U.length + 1 by omega] at hB; simpa using hB
    subst hXA hYB
    have hxy : x = flipL y := by rw [← hX, ← hY]; exact hAB
    obtain ⟨hcap, hlet⟩ := tmLay_cap v w x y
    have hrE : U.length + 1 < (run flipL E).length := by
      rw [hiso.length_eq, hT]; simp
    obtain ⟨U', X', Y', W', hE, hU'⟩ := exists_split_cross hrE
    have hsnd := hiso.1
    rw [hE, hT] at hsnd
    simp only [List.map_append, List.map_cons] at hsnd
    obtain ⟨e1, e2⟩ := List.append_inj hsnd (by simp [hU'])
    simp only [List.cons.injEq] at e2
    obtain ⟨eX, eY, eW⟩ := e2
    have hne' : X'.1 ≠ Y'.1 := by
      intro e
      have hs : Chord.Same (run flipL E) U.length (U.length + 1) := by
        refine ⟨by omega, ?_, ?_⟩
        · rw [Chord.idAt_ne_none_iff]; omega
        · rw [hE, ← hU']; simp [Chord.idAt, e]
      have := ((hiso.2 _ _).1 hs).2.2
      rw [hT] at this
      apply hne
      simpa [Chord.idAt] using this
    obtain ⟨E', hf', hiso', hle, hxl⟩ := capPush (r3Rel cs) μ E hf U' [] W' X' Y'
      (by rw [hE]; simp) (by rw [eX, eY, hX, hY]; exact hxy) hne'
    have hjnE : jn (run flipL E) U.length = (U' ++ [] ++ W').map (rl Y'.1 X'.1) := by
      rw [hE, ← hU', List.append_nil]
      have := Chord.jn_mid U' W' X' Y'
      simpa using this
    have hkg : k + v.length = U.length := by omega
    have hstst : (tStep flipL k T (.cap v.length)).st = jn T.st U.length := by
      simp only [tStep]; rw [hkg]
    have hjnT : jn T.st U.length = (U ++ W).map (rl Y.1 X.1) := by
      rw [hT]; have := Chord.jn_mid U W X Y; simpa using this
    refine ⟨?_, ?_, ?_, E', hf', ?_, by simpa [ncr₂] using hle, fun h => ?_⟩
    · rw [hstst, hjnT, Chord.map_snd_map_rl, hlet]
      simp [h1, h2]
    · rw [hcap, hlet, hxy]
      have := (xChain_xCapL y).whisk v w
      simpa using this
    · rw [hcap]; simp [ncr₂]
    · rw [hstst]
      exact hiso'.trans (hjnE ▸ hiso.jn (by rw [hiso.length_eq.symm] at hr; omega))
    · have H := hxl (by simpa [ncr₂] using h)
      simp only [List.map_nil, capBlk_nil, List.append_nil, List.map_append] at H
      rw [e1, eW, eY, hY, h1, h2, List.append_assoc] at H
      rw [hlet, hcap, map_xwhL_xwhL]
      refine XLt.congr ?_ rfl (H.mono (by simp [ncr₂]))
      simp

/-- **A matching on top of a one-sided diagram** is, up to sign modulo diagrams with fewer
crossings, a one-sided diagram with the pairing of the matching and at most as many crossings
(when it has fewer, no relation is claimed). -/
theorem tProcess (μ : X) {k : ℕ} {u : List (Letter I)} (hu : u.length = k) :
    ∀ (R : List (TMove (Letter I))) (T : TState (Letter I)) (l : List (Letter I))
      (E : List (Move (Letter I))), TInv T → Fits 0 E → Iso (run flipL E) T.st →
      T.st.map Prod.snd = u ++ l → TFits flipL k T R →
      (tRun flipL k T R).st.map Prod.snd = u ++ R.foldl tLet l ∧
      XChain l (tLay l R) (R.foldl tLet l) ∧ xcnt (tLay l R) = ncr₂ R ∧
      ∃ E', Fits 0 E' ∧ Iso (run flipL E') (tRun flipL k T R).st ∧ ncr E' ≤ ncr E + ncr₂ R ∧
        (ncr E' = ncr E + ncr₂ R → XLt cs μ [] (u ++ R.foldl tLet l) (ncr E + ncr₂ R)
          (chordLay [] E ++ (tLay l R).map (xwhL u [])) (chordLay [] E'))
  | [], T, l, E, _, hf, hiso, hl, _ =>
    ⟨hl, rfl, rfl, E, hf, hiso, by simp [ncr₂], fun _ => by simpa [tLay] using XLt.refl _⟩
  | m :: R, T, l, E, I₀, hf, hiso, hl, ⟨hm, hR⟩ => by
    obtain ⟨hl₁, hc₁, hx₁, E₁, hf₁, hiso₁, hle₁, hxl₁⟩ := tPush cs μ I₀ hf hiso hu hl hm
    obtain ⟨hl₂, hc₂, hx₂, E', hf', hiso', hle', hxl'⟩ :=
      tProcess μ hu R _ _ E₁ (I₀.step hm) hf₁ hiso₁ hl₁ hR
    have hn := ncr₂_cons m R
    refine ⟨hl₂, hc₁.append hc₂, by rw [tLay, xcnt_append, hx₁, hx₂, hn], E', hf', hiso',
      by omega, fun h => ?_⟩
    have h₁ : ncr E₁ = ncr E + ncr₂ [m] := by omega
    have H₁ := hxl₁ h₁
    have H₂ := hxl' (by omega)
    have hchE : XChain [] (chordLay [] E) (u ++ l) := by
      rw [← hl, ← hiso.1]; exact xChain_run hf
    have hch₁ : XChain [] (chordLay [] E₁) (u ++ tLet l m) := by
      rw [← hl₁, ← hiso₁.1]; exact xChain_run hf₁
    have hL₀ : XChain [] (chordLay [] E ++ (tmLay l m).map (xwhL u [])) (u ++ tLet l m) :=
      hchE.append (by simpa using hc₁.whisk u [])
    have H₃ := H₁.append_right (t := u ++ (m :: R).foldl tLet l) hL₀ hch₁
      ((tLay (tLet l m) R).map (xwhL u []))
    rw [xcnt_map_xwhL, hx₂, ← h₁] at H₃
    refine XLt.congr ?_ rfl ((H₃.trans H₂).mono (by omega))
    simp [tLay, List.append_assoc]

variable {cs}

theorem bendG_mem_ltL (μ : X) {s t : List (Letter I)} {n : ℕ}
    {g : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ (dualW s ++ t))}
    (hg : g ∈ LtL D Sc cs μ [] (dualW s ++ t) n) : bendG cs μ s t g ∈ LtL D Sc cs μ s t n := by
  rcases n with _ | c
  · have : g = 0 := by
      have h0 : LtL D Sc cs μ [] (dualW s ++ t) 0 = ⊥ := by
        rw [LtL, Submodule.span_eq_bot]
        rintro _ ⟨L, hL, -⟩; omega
      rw [h0] at hg; exact hg
    rw [this, map_zero]; exact Submodule.zero_mem _
  · exact leL_le_ltL (Nat.lt_succ_self c) (bendG_mem_leL cs μ (ltL_le_leL le_rfl hg))

/-- **Bending back a relation between bent diagrams.** -/
theorem xlt_bendG (μ : X) {s t : List (Letter I)} {n : ℕ} {A C : List (XLayer I)}
    (hA : XChain s A t) (hC : XChain [] C (dualW s ++ t))
    (h : XLt cs μ [] (dualW s ++ t) n (cupA (dualW s) ++ A.map (xwhL (dualW s) [])) C) :
    XLt cs μ s t n A (bendL s t C) := by
  obtain ⟨p, hp⟩ := h
  rw [← bendF_xev cs μ hA] at hp
  have H := bendG_mem_ltL μ hp
  rw [map_sub, map_smul, bendG_bendF_xev cs μ hA, bendG_xev cs μ hC] at H
  set q := pairPar D μ (dualW s) + cupsPar D μ (dualW s) * xpar D μ A
  refine ⟨q + p, ?_⟩
  have H' := Submodule.smul_mem _ (zsign k q) H
  rwa [smul_sub, smul_smul, smul_smul, zsign_mul_self', one_smul, ← zsign_add] at H'

variable (cs)

/-- **[BE2] §8, reduced matchings: the normal form.** A reduced `(a, b)`-matching has as many
crossings as the crossing number of its pairing, and agrees up to sign, modulo diagrams with fewer
crossings, with the canonical chord diagram of its pairing (on `a* b`) bent back by nested caps.

This is the step of the proof of [BE2] Theorem 8.1 (after KL III Proposition 3.11) that makes the
choice of reduced representatives irrelevant; `Reduced₂` does not ask that every strand has at
most one critical point. -/
theorem reduced₂_normal_form (μ : X) {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a b R) (hred : Reduced₂ a R) :
    ncr₂ R = Chord.cr (pairing₂ a R) ∧
      XLt cs μ a b (ncr₂ R) (tLay a R) (bendL a b (chordLay [] (canon (pairing₂ a R)))) := by
  obtain ⟨hfit, hb⟩ := hR
  obtain ⟨hf₀, hn₀, hc₀, hw₀⟩ := cupMoves_spec (dualW a)
  rw [dualW_dualW] at hw₀
  have hu : (dualW a).length = a.length := by simp [dualW]
  have I₀ : TInv (tStart a) := Chord.tInv_start hf₀ hn₀
  have hl₀ : (tStart a).st.map Prod.snd = dualW a ++ a := by
    rw [tStart]; dsimp only; rw [← foldl_chStep_eq, hw₀]
  obtain ⟨hl, hc, -, E', hf', hiso', hle, hxl⟩ := tProcess cs μ hu R (tStart a) a
    (cupMoves (dualW a)) I₀ hf₀ (Iso.refl _) hl₀ hfit
  rw [hb] at hl hc hxl
  -- the parity bound
  have I := I₀.run hfit
  have hlen := Chord.length_xs_tRun flipL a.length R (tStart a)
  have hbound := Chord.length_xs_le_cr I hred.1 hred.2
  rw [hlen, show (tStart a).xs.length = 0 from rfl, zero_add] at hbound
  change ncr₂ R ≤ Chord.cr (pairing₂ a R) at hbound
  have hcr : Chord.cr (run flipL E') = Chord.cr (pairing₂ a R) :=
    le_antisymm (Chord.cr_le_of_iso hiso') (Chord.cr_le_of_iso hiso'.symm)
  have hcr' := Chord.cr_run_le_ncr flipL hf'
  rw [hn₀, zero_add] at hle hxl
  have hpr : pairing₂ a R = (tRun flipL a.length (tStart a) R).st := rfl
  have heq : ncr E' = ncr₂ R := by omega
  refine ⟨by omega, ?_⟩
  -- the one-sided diagram is reduced, hence equivalent to the canonical diagram
  have hredE : Chord.Reduced flipL E' := (Chord.reduced_iff flipL hf').2 (by omega)
  have hequiv := Chord.equiv_canon_of_reduced flipL hf' hredE
  obtain ⟨-, hsound⟩ := equiv_sound (r3Rel cs) hequiv hf'
  rw [Chord.canon_eq_of_iso hiso'] at hsound
  rw [heq] at hsound
  have H := (hxl heq).trans (hsound μ (dualW a ++ b))
  rw [hc₀] at H
  have hv : Chord.Valid (pairing₂ a R) := I.valid
  have hlet : Chord.Lettered flipL (pairing₂ a R) :=
    lettered_of_iso hiso' (Chord.lettered_run flipL_involutive hf')
  have hC : XChain [] (chordLay [] (canon (pairing₂ a R))) (dualW a ++ b) := by
    have := xChain_chordLay_canon hv hlet; rwa [hpr, hl] at this
  exact xlt_bendG μ hc hC H

end OddMath.SKM
