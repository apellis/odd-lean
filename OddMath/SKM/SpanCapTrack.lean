/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChordJoin
import OddMath.SKM.SpanCapCup
import OddMath.SKM.SpanR3
import OddMath.SKM.SpanOneSided

/-!
# The cap push, keeping track of the pairing

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1, whose proof the paper omits, referring to M. Khovanov, A. Lauda, *A categorification
of quantum `sl(n)`*, arXiv:0807.3250v1, Proposition 3.11. As in the proof of KL III Proposition
3.11, a cap on top of a diagram of cups and crossings is pushed down until it disappears. Here the
push keeps track of the result: the cap block `capBlk S l 0` (the strand `B = l` moves left across
the strands `S`, then the cap joins it to `A = l*`) on top of a chord diagram `D` is, up to sign
modulo diagrams with fewer crossings, a chord diagram `D'` whose pairing is that of `D` with the
strands `A` and `B` joined (`Chord.rl`), with at most as many crossings; when `D'` has fewer
crossings, no relation is claimed (`CapPushRes`).

The steps use the local relations of `OddMath.SKM.SpanCapCross` and `OddMath.SKM.SpanCapCup`: a
strand entering the block from either side (`capBlk_enterL`, `capBlk_enterR`), a crossing of two
strands of the block (Reidemeister 3, `capBlk_crossS`), the zigzags (`capBlk_cupAleft0`,
`capBlk_cupBright0`, `zigR`), and the super interchange law for moves away from the block. A
crossing or a cup forming a curl or a double crossing with the block only lowers the number of
crossings of the result.

## Main results

* `chordLay_mvL`, `chordLay_mvR`: a strand moving across a block of strands, as a chord diagram.
* `capPush`: **the cap push**, keeping track of the pairing and the number of crossings.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation
open StringDiagrams.Chord (Move Fits run Iso rl rlId mvL mvR rl_of_ne rl_of_eq)

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} {cs : CScalars Sc}

/-! ## Chord diagrams read one move at a time -/

theorem run_snoc (E : List (Move (Letter I))) (m : Move (Letter I)) :
    run flipL (E ++ [m]) = Chord.step flipL (run flipL E) m := by
  rw [Chord.run_append]; rfl

theorem foldl_chStep_eq (E : List (Move (Letter I))) :
    E.foldl chStep [] = (run flipL E).map Prod.snd := (Chord.snd_run E).symm

theorem chordLay_snoc (E : List (Move (Letter I))) (m : Move (Letter I)) :
    chordLay [] (E ++ [m]) = chordLay [] E ++ moveLay ((run flipL E).map Prod.snd) m := by
  rw [chordLay_append, foldl_chStep_eq]; simp [chordLay]

theorem xChain_run {E : List (Move (Letter I))} (hf : Fits 0 E) :
    XChain [] (chordLay [] E) ((run flipL E).map Prod.snd) := by
  have := xChain_chordLay (l := []) hf; rwa [foldl_chStep_eq] at this

theorem fits_snoc' {E : List (Move (Letter I))} {m : Move (Letter I)} :
    Fits 0 (E ++ [m]) ↔ Fits 0 E ∧ m.Ok (run flipL E).length :=
  Chord.fits_snoc

theorem fits_append_run {E F : List (Move (Letter I))} (hE : Fits 0 E)
    (hF : Fits (run flipL E).length F) : Fits 0 (E ++ F) := by
  rw [Chord.fits_append]
  refine ⟨hE, ?_⟩
  rwa [show E.foldl Move.len 0 = (run flipL E).length by
    rw [Chord.run, Chord.length_foldl_step]; rfl]

theorem run_append_foldl (E F : List (Move (Letter I))) :
    run flipL (E ++ F) = F.foldl (Chord.step flipL) (run flipL E) := Chord.run_append E F

/-! ## A strand moving across a block -/

theorem chordLay_mvL : ∀ (u S Q : List (Letter I)) (b : Letter I),
    chordLay (u ++ S ++ [b] ++ Q) (mvL u.length S.length) = (lmLc S b).map (xwhL u Q)
  | u, [], Q, b => by simp [mvL, chordLay, lmLc]
  | u, x :: S, Q, b => by
    have e1 : u ++ (x :: S) ++ [b] ++ Q = (u ++ [x]) ++ S ++ [b] ++ Q := by simp
    have e2 : u.length + 1 = (u ++ [x]).length := by simp
    have hf := Chord.foldl_mvL (α := Letter I) chStep (fun _ _ => rfl) (u ++ [x]) S Q b
    rw [List.length_cons, Chord.mvL, chordLay_append, e1, e2, chordLay_mvL (u ++ [x]) S Q b, hf]
    have e3 : u ++ [x] ++ [b] ++ S ++ Q = u ++ x :: b :: (S ++ Q) := by simp
    rw [e3]
    simp only [chordLay, List.append_nil]
    rw [moveLay_cross]
    simp [lmLc]

theorem chordLay_mvR : ∀ (u S Q : List (Letter I)) (a : Letter I),
    chordLay (u ++ [a] ++ S ++ Q) (mvR u.length S.length) = (lmRc a S).map (xwhL u Q)
  | u, [], Q, a => by simp [mvR, chordLay, lmRc]
  | u, x :: S, Q, a => by
    have e3 : u ++ [a] ++ (x :: S) ++ Q = u ++ a :: x :: (S ++ Q) := by simp
    have e4 : chStep (u ++ a :: x :: (S ++ Q)) (.cross u.length) = (u ++ [x]) ++ [a] ++ S ++ Q := by
      rw [chStep_cross]; simp
    have e2 : u.length + 1 = (u ++ [x]).length := by simp
    rw [List.length_cons, Chord.mvR, e3, chordLay, moveLay_cross, e4, e2,
      chordLay_mvR (u ++ [x]) S Q a]
    simp [lmRc]

/-! ## The statement of the cap push -/

variable (cs) in
/-- The conclusion of the cap push for the block `P A S B Q` on top of `E`: a chord diagram `E'`
whose pairing is that of `E` with `A` and `B` joined, with at most as many crossings as the block
on top of `E`, and agreeing with it up to sign modulo fewer crossings when it has as many. -/
def CapPushRes (μ : X) (E : List (Move (Letter I))) (P S Q : List (ℕ × Letter I))
    (A B : ℕ × Letter I) : Prop :=
  ∃ E', Fits 0 E' ∧ Iso (run flipL E') ((P ++ S ++ Q).map (rl B.1 A.1)) ∧
    ncr E' ≤ ncr E + S.length ∧
    (ncr E' = ncr E + S.length → XLt cs μ [] ((P ++ S ++ Q).map Prod.snd) (ncr E + S.length)
      (chordLay [] E ++ (capBlk (S.map Prod.snd) B.2 0).map
        (xwhL (P.map Prod.snd) (Q.map Prod.snd)))
      (chordLay [] E'))

variable (cs) in
/-- The cap push holds for every block on top of `E`. -/
def CapPush (μ : X) (E : List (Move (Letter I))) : Prop :=
  ∀ (P S Q : List (ℕ × Letter I)) (A B : ℕ × Letter I),
    run flipL E = P ++ [A] ++ S ++ [B] ++ Q → A.2 = flipL B.2 → A.1 ≠ B.1 →
      CapPushRes cs μ E P S Q A B

variable {μ : X}

theorem xChain_blk {P S Q : List (ℕ × Letter I)} {A B : ℕ × Letter I} (hl : A.2 = flipL B.2) :
    XChain ((P ++ [A] ++ S ++ [B] ++ Q).map Prod.snd)
      ((capBlk (S.map Prod.snd) B.2 0).map (xwhL (P.map Prod.snd) (Q.map Prod.snd)))
      ((P ++ S ++ Q).map Prod.snd) := by
  have := (xChain_capBlk (S.map Prod.snd) B.2 0).whisk (P.map Prod.snd) (Q.map Prod.snd)
  simpa [hl] using this

/-- A result with fewer crossings needs no relation. -/
theorem capPushRes_of_lt {E E' : List (Move (Letter I))} {P S Q : List (ℕ × Letter I)}
    {A B : ℕ × Letter I} (hf : Fits 0 E')
    (hiso : Iso (run flipL E') ((P ++ S ++ Q).map (rl B.1 A.1))) (hlt : ncr E' < ncr E + S.length) :
    CapPushRes cs μ E P S Q A B :=
  ⟨E', hf, hiso, hlt.le, fun h => absurd h hlt.ne⟩

/-- Appending a move to the result of a cap push. -/
theorem xlt_snoc {E' : List (Move (Letter I))} {T : List (ℕ × Letter I)} (hf : Fits 0 E')
    (hiso : Iso (run flipL E') T) {l : List (Letter I)} (hT : T.map Prod.snd = l)
    {L₀ : List (XLayer I)} {n n' : ℕ}
    (hL₀ : XChain [] L₀ l) (h : XLt cs μ [] l n L₀ (chordLay [] E'))
    {m : Move (Letter I)} (hm : m.Ok l.length) {M : List (XLayer I)} (hM : moveLay l m = M)
    (hn : n + ncr [m] ≤ n') (t : List (Letter I)) :
    XLt cs μ [] t n' (L₀ ++ M) (chordLay [] (E' ++ [m])) := by
  rw [chordLay_snoc, hiso.1, hT, hM]
  refine (h.append_right hL₀ (by rw [← hT, ← hiso.1]; exact xChain_run hf) M).mono ?_
  rw [← hM, xcnt_moveLay hm]; exact hn

theorem swapAt_map_mid {β γ : Type*} (f : β → γ) (u w : List β) (x y : β) :
    Chord.swapAt ((u ++ x :: y :: w).map f) u.length = (u ++ y :: x :: w).map f := by
  simpa using swapAt_mid (u.map f) (w.map f) (f x) (f y)

theorem iso_snoc_cross {E' : List (Move (Letter I))} {T T' : List (ℕ × Letter I)}
    (hiso : Iso (run flipL E') T) {f : ℕ × Letter I → ℕ × Letter I} {u w : List (ℕ × Letter I)}
    {x y : ℕ × Letter I} {q : ℕ} (hT : T = (u ++ x :: y :: w).map f)
    (hT' : T' = (u ++ y :: x :: w).map f) (hq : q = u.length) :
    Iso (run flipL (E' ++ [.cross q])) T' := by
  subst hT hT' hq
  rw [run_snoc]
  show Iso (Chord.swapAt (run flipL E') u.length) _
  have := hiso.swapAt u.length
  rwa [swapAt_map_mid] at this

theorem iso_snoc_cup {E' : List (Move (Letter I))} {T T' : List (ℕ × Letter I)} (hf : Fits 0 E')
    (hiso : Iso (run flipL E') T) {f : ℕ × Letter I → ℕ × Letter I} {u w : List (ℕ × Letter I)}
    {y z : ℕ × Letter I} {g n : ℕ} {a : Letter I} (hT : T = (u ++ w).map f)
    (hT' : T' = (u ++ y :: z :: w).map f) (hg : g = u.length) (hy : f y = (n, a))
    (hz : f z = (n, flipL a)) (hn : ∀ x ∈ T, x.1 ≠ n) :
    Iso (run flipL (E' ++ [.cup g a])) T' := by
  rw [run_snoc]
  show Iso (Chord.insAt (run flipL E') g ((run flipL E').length, a)
    ((run flipL E').length, flipL a)) T'
  have := hiso.insAt (g := g) (by rw [hiso.length_eq, hT, hg]; simp)
    (fun x hx => ((Chord.inv_run (d := flipL) hf).2 x hx).ne) hn a (flipL a)
  convert this using 1
  subst hT hT' hg
  simp [Chord.insAt, hy, hz]

/-- Closes an equation between lists up to associativity. -/
macro "lsimp" : tactic => `(tactic| first | rfl | simp | (simp only [List.append_assoc,
  List.cons_append, List.singleton_append, List.nil_append]))

/-- Arithmetic of crossing numbers and lengths. -/
macro "nomega" : tactic => `(tactic| (
  simp only [ncr_append, ncr_cons_cross, ncr_cons_cup, ncr_nil, List.length_append,
    List.length_cons, List.length_nil, List.length_singleton, List.length_map] at *
  omega))

theorem flipL_inj {a b : Letter I} (h : flipL a = flipL b) : a = b := by
  rw [← flipL_flipL a, h, flipL_flipL]

theorem ok_cross {q : ℕ} {l : List (Letter I)} (h : q + 1 < l.length) :
    (Move.cross (α := Letter I) q).Ok l.length := h

/-! ## The cap push through a crossing -/

theorem capPush_cross (hR : R3Rel D Sc cs) {E : List (Move (Letter I))} (ih : CapPush cs μ E)
    (hfE : Fits 0 E) {p : ℕ} (hp : p + 1 < (run flipL E).length) :
    CapPush cs μ (E ++ [.cross p]) := by
  intro P S Q A B ht hl hne
  obtain ⟨u, x, y, w, ht₀, hu⟩ := exists_split_cross hp
  have hncr : ncr (E ++ [.cross p]) = ncr E + 1 := by rw [ncr_append]; rfl
  have hchE := xChain_run hfE
  rw [ht₀] at hchE
  have hlay : chordLay [] (E ++ [.cross p]) =
      chordLay [] E ++ (xCrL x.2 y.2).map (xwhL (u.map Prod.snd) (w.map Prod.snd)) := by
    rw [chordLay_snoc, ht₀]
    exact congrArg _ (moveLay_cross_eq (by simp) (by simp [hu]))
  rw [run_snoc, ht₀] at ht
  change Chord.swapAt (u ++ x :: y :: w) p = _ at ht
  rw [← hu, swapAt_mid] at ht
  have hxE : xcnt (chordLay [] E) = ncr E := xcnt_chordLay (l := []) hfE
  unfold CapPushRes
  rw [hncr, hlay]
  rcases posPair (show u ++ [y, x] ++ w = P ++ [A] ++ S ++ [B] ++ Q by simpa using ht) with
    ⟨R, hP, hw⟩ | ⟨hP, h1, hv⟩ | ⟨hu', h2, S', hS, hv⟩ | ⟨hu', h2, hS, h1, hv⟩ |
    ⟨S₁, S₂, hS, hu', hv⟩ | ⟨S', hS, h1, hu', hv⟩ | ⟨hu', h2, hQ⟩ | ⟨R, hQ, hu'⟩
  · -- a crossing to the left of the block
    subst hP hw
    obtain ⟨E', hf', hiso, hle, hxl⟩ := ih (u ++ [x, y] ++ R) S Q A B (by rw [ht₀]; simp) hl hne
    refine ⟨E' ++ [.cross u.length], fits_snoc'.2 ⟨hf', by
        rw [hiso.length_eq]; show _ + 1 < _; simp only [List.length_map, List.length_append,
          List.length_cons, List.length_nil]; omega⟩,
      iso_snoc_cross hiso (f := rl B.1 A.1) (u := u) (x := x) (y := y) (w := R ++ S ++ Q) (by lsimp) (by lsimp) rfl,
      by nomega, fun h => ?_⟩
    have I := hxl (by nomega)
    have H := xlt_snoc (μ := μ) (n' := ncr E + 1 + S.length) hf' hiso (by simp)
      (hchE.app (xChain_blk (P := u ++ [x, y] ++ R) (S := S) (Q := Q) hl) (by simp)) I
      (m := .cross u.length) (ok_cross (by simp)) (moveLay_cross_eq (u := u.map Prod.snd)
        (x := x.2) (y := y.2) (w := (R ++ S ++ Q).map Prod.snd) (by simp) (by simp))
      (by nomega) ((u ++ [y, x] ++ R ++ S ++ Q).map Prod.snd)
    refine XLt.trans ?_ H
    exact XLt.ichg (chordLay [] E) [] (u.map Prod.snd) (Q.map Prod.snd) (xChain_xCrL x.2 y.2)
      ((xChain_capBlk (S.map Prod.snd) B.2 0).whisk (R.map Prod.snd) [])
      (hchE.cast rfl (by simp [hl])) (by simp [hl]) (by simp)
  · -- the strand to the left of `A` enters the block
    subst hP hv h1
    obtain ⟨E', hf', hiso, hle, hxl⟩ := ih u (y :: S) Q x B (by rw [ht₀]; simp) hl hne
    refine ⟨E', hf', by simpa using hiso, by nomega, fun h => ?_⟩
    have I := hxl (by nomega)
    refine XLt.trans ?_ (XLt.congr rfl rfl (by simpa using I.mono (by simp; omega)))
    refine XLt.at (chordLay [] E) [] (u.map Prod.snd) (Q.map Prod.snd)
      (capBlk_enterL cs _ (S.map Prod.snd) y.2 B.2 0) (hchE.cast rfl (by simp [hl])) ?_ ?_ ?_ ?_ ?_
    · have h1 := (xChain_xCrL (flipL B.2) y.2).whisk [] (S.map Prod.snd ++ [B.2])
      have h2 := (xChain_capBlk (S.map Prod.snd) B.2 0).whisk [y.2] []
      exact (h1.app h2 (by simp)).cast (by simp) (by simp)
    · simpa using xChain_capBlk (y.2 :: S.map Prod.snd) B.2 0
    · simp [hl]
    · simp
    · simp [hxE]
  · -- a crossing of `A` with the first strand of the block: lower
    subst hu' h2 hS hv
    obtain ⟨E', hf', hiso, hle, -⟩ := ih (u ++ [x]) S' Q y B (by rw [ht₀]; simp) hl hne
    exact ⟨E', hf', by simpa using hiso, by nomega,
      fun h => absurd h (by nomega)⟩
  · -- a crossing of `A` and `B`: a curl, lower
    subst hu' h2 hS h1 hv
    obtain ⟨E', hf', hiso, hle, -⟩ := ih u [] w x y (by rw [ht₀]; simp)
      (by rw [hl, flipL_flipL]) (Ne.symm hne)
    exact ⟨E', hf', hiso.trans (by simpa using Chord.iso_map_rl_comm hne (u ++ w)),
      by nomega, fun h => absurd h (by nomega)⟩
  · -- a crossing of two strands of the block: Reidemeister 3
    subst hS hu' hv
    obtain ⟨E', hf', hiso, hle, hxl⟩ :=
      ih P (S₁ ++ [x, y] ++ S₂) Q A B (by rw [ht₀]; simp) hl hne
    refine ⟨E' ++ [.cross (P.length + S₁.length)], fits_snoc'.2 ⟨hf', by
        rw [hiso.length_eq]; show _ + 1 < _; simp only [List.length_map, List.length_append,
          List.length_cons, List.length_nil]; omega⟩,
      iso_snoc_cross hiso (f := rl B.1 A.1) (u := P ++ S₁) (x := x) (y := y) (w := S₂ ++ Q) (by lsimp) (by lsimp)
        (by simp), by nomega, fun h => ?_⟩
    have I := hxl (by nomega)
    have H := xlt_snoc (μ := μ) (n' := ncr E + 1 + (S₁ ++ [y, x] ++ S₂).length) hf' hiso
      (by simp) (hchE.app (xChain_blk (P := P) (S := S₁ ++ [x, y] ++ S₂) (Q := Q) hl) (by simp)) I
      (m := .cross (P.length + S₁.length)) (ok_cross (by first | omega | (simp; omega)))
      (moveLay_cross_eq (u := (P ++ S₁).map Prod.snd) (x := x.2) (y := y.2)
        (w := (S₂ ++ Q).map Prod.snd) (by simp) (by simp))
      (by nomega) ((P ++ (S₁ ++ [y, x] ++ S₂) ++ Q).map Prod.snd)
    refine XLt.trans ?_ H
    refine XLt.at (chordLay [] E) [] (P.map Prod.snd) (Q.map Prod.snd)
      (capBlk_crossS cs hR _ (S₁.map Prod.snd) (S₂.map Prod.snd) x.2 y.2 B.2 0)
      (hchE.cast rfl (by simp [hl])) ?_ ?_ ?_ ?_ ?_
    · have h1 := (xChain_xCrL x.2 y.2).whisk ([flipL B.2] ++ S₁.map Prod.snd)
        (S₂.map Prod.snd ++ [B.2])
      have h2 := xChain_capBlk (S₁.map Prod.snd ++ [y.2, x.2] ++ S₂.map Prod.snd) B.2 0
      exact (h1.app h2 (by simp)).cast (by simp) (by simp)
    · have h1 := xChain_capBlk (S₁.map Prod.snd ++ [x.2, y.2] ++ S₂.map Prod.snd) B.2 0
      have h2 := (xChain_xCrL x.2 y.2).whisk (S₁.map Prod.snd) (S₂.map Prod.snd)
      exact (h1.app h2 (by simp)).cast (by simp) (by simp)
    · simp [hl]
    · simp
    · simp [hxE]; omega
  · -- a crossing of the last strand of the block with `B`: lower
    subst hS h1 hu' hv
    obtain ⟨E', hf', hiso, hle, -⟩ := ih P S' (y :: w) A x (by rw [ht₀]; simp) hl hne
    exact ⟨E', hf', by simpa using hiso, by nomega,
      fun h => absurd h (by nomega)⟩
  · -- the strand to the right of `B` enters the block
    subst hu' h2 hQ
    obtain ⟨E', hf', hiso, hle, hxl⟩ := ih P (S ++ [x]) w A y (by rw [ht₀]; simp) hl hne
    refine ⟨E', hf', by simpa using hiso, by nomega, fun h => ?_⟩
    have I := hxl (by nomega)
    refine XLt.congr ?_ rfl (by simpa using I.mono (by simp; omega))
    rw [← capBlk_enterR]
    simp [hl]
  · -- a crossing to the right of the block
    subst hQ hu'
    obtain ⟨E', hf', hiso, hle, hxl⟩ := ih P S (R ++ [x, y] ++ w) A B (by rw [ht₀]; simp) hl hne
    refine ⟨E' ++ [.cross (P.length + S.length + R.length)], fits_snoc'.2 ⟨hf', by
        rw [hiso.length_eq]; show _ + 1 < _; simp only [List.length_map, List.length_append,
          List.length_cons, List.length_nil]; omega⟩,
      iso_snoc_cross hiso (f := rl B.1 A.1) (u := P ++ S ++ R) (x := x) (y := y) (w := w) (by lsimp) (by lsimp)
        (by simp; omega), by nomega, fun h => ?_⟩
    have I := hxl (by nomega)
    have H := xlt_snoc (μ := μ) (n' := ncr E + 1 + S.length) hf' hiso (by simp)
      (hchE.app (xChain_blk (P := P) (S := S) (Q := R ++ [x, y] ++ w) hl) (by simp)) I
      (m := .cross (P.length + S.length + R.length)) (ok_cross (by first | omega | (simp; omega)))
      (moveLay_cross_eq (u := (P ++ S ++ R).map Prod.snd) (x := x.2) (y := y.2)
        (w := w.map Prod.snd) (by simp) (by simp; omega))
      (by nomega) ((P ++ S ++ (R ++ [y, x] ++ w)).map Prod.snd)
    refine XLt.trans ?_ H
    refine XLt.symm (XLt.ichg (chordLay [] E) [] (P.map Prod.snd) (w.map Prod.snd)
      (xChain_capBlk (S.map Prod.snd) B.2 0)
      ((xChain_xCrL x.2 y.2).whisk (R.map Prod.snd) []) (hchE.cast rfl (by simp [hl])) ?_ ?_)
    · simp
    · simp [hl]

/-! ## The cap push through a cup -/

theorem fresh_map_rl {L : List (ℕ × Letter I)} {n b a : ℕ} (hL : ∀ x ∈ L, x.1 < n) (ha : a < n) :
    ∀ x ∈ L.map (rl b a), x.1 ≠ n := by
  intro x hx
  obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hx
  have := hL x' hx'
  simp only [rl, rlId]; split_ifs <;> omega

theorem capPush_cup {E : List (Move (Letter I))} (ih : CapPush cs μ E) (hfE : Fits 0 E) {g : ℕ}
    (hg : g ≤ (run flipL E).length) (a : Letter I) : CapPush cs μ (E ++ [.cup g a]) := by
  intro P S Q A B ht hl hne
  obtain ⟨u, w, ht₀, hu⟩ := exists_split_cup hg
  set n := (run flipL E).length with hn
  have hfr : ∀ x ∈ run flipL E, x.1 < n := (Chord.inv_run (d := flipL) hfE).2
  have hncr : ncr (E ++ [.cup g a]) = ncr E := by rw [ncr_append]; rfl
  have hchE := xChain_run hfE
  rw [ht₀] at hchE
  have hlay : chordLay [] (E ++ [.cup g a]) =
      chordLay [] E ++ (xCupL a).map (xwhL (u.map Prod.snd) (w.map Prod.snd)) := by
    rw [chordLay_snoc, ht₀]
    exact congrArg _ (moveLay_cup_eq a (by simp) (by simp [hu]))
  rw [run_snoc] at ht
  change Chord.insAt (run flipL E) g (n, a) (n, flipL a) = _ at ht
  rw [ht₀, ← hu] at ht
  simp only [Chord.insAt, List.take_left', List.drop_left'] at ht
  have hxE : xcnt (chordLay [] E) = ncr E := xcnt_chordLay (l := []) hfE
  have hcE : ∀ F, chordLay [] (E ++ F) = chordLay [] E ++ chordLay ((run flipL E).map Prod.snd) F :=
    fun F => by rw [chordLay_append, foldl_chStep_eq]
  unfold CapPushRes
  rw [hncr, hlay]
  rcases posPair (show u ++ [(n, a), (n, flipL a)] ++ w = P ++ [A] ++ S ++ [B] ++ Q by
      simpa using ht) with
    ⟨R, hP, hw⟩ | ⟨hP, h1, hv⟩ | ⟨hu', h2, S', hS, hv⟩ | ⟨hu', h2, hS, h1, hv⟩ |
    ⟨S₁, S₂, hS, hu', hv⟩ | ⟨S', hS, h1, hu', hv⟩ | ⟨hu', h2, hQ⟩ | ⟨R, hQ, hu'⟩
  · -- a cup to the left of the block
    subst hP hw
    have hAB : A.1 < n ∧ B.1 < n := ⟨hfr A (by rw [ht₀]; simp), hfr B (by rw [ht₀]; simp)⟩
    obtain ⟨E', hf', hiso, hle, hxl⟩ := ih (u ++ R) S Q A B (by rw [ht₀]; simp) hl hne
    refine ⟨E' ++ [.cup u.length a], fits_snoc'.2 ⟨hf', by
        rw [hiso.length_eq]; show _ ≤ _; simp only [List.length_map, List.length_append]; omega⟩,
      iso_snoc_cup hf' hiso (f := rl B.1 A.1) (u := u) (w := R ++ S ++ Q) (by lsimp) (by lsimp)
        rfl (rl_of_ne (by simp; omega)) (rl_of_ne (by simp; omega))
        (fresh_map_rl (fun x hx => hfr x (by rw [ht₀]; simp at hx ⊢; tauto)) hAB.1),
      by nomega, fun h => ?_⟩
    have I := hxl (by nomega)
    have H := xlt_snoc (μ := μ) (n' := ncr E + S.length) hf' hiso (by simp)
      (hchE.app (xChain_blk (P := u ++ R) (S := S) (Q := Q) hl) (by simp)) I
      (m := .cup u.length a) (show _ ≤ _ by simp)
      (moveLay_cup_eq (u := u.map Prod.snd) (w := (R ++ S ++ Q).map Prod.snd) a (by simp)
        (by simp)) (by nomega) ((u ++ [(n, a), (n, flipL a)] ++ R ++ S ++ Q).map Prod.snd)
    refine XLt.trans ?_ H
    exact XLt.ichg (chordLay [] E) [] (u.map Prod.snd) (Q.map Prod.snd) (xChain_xCupL a)
      ((xChain_capBlk (S.map Prod.snd) B.2 0).whisk (R.map Prod.snd) [])
      (hchE.cast rfl (by simp [hl])) (by simp [hl]) (by simp)
  · -- the cup creates `A` and the strand to its left: a zigzag
    subst hP hv
    obtain rfl : (n, flipL a) = A := h1
    have ha : a = B.2 := flipL_inj hl
    subst ha
    have hrun : run flipL (E ++ mvL u.length S.length) = u ++ [B] ++ S ++ Q := by
      rw [run_append_foldl, ht₀,
        show u ++ (S ++ [B] ++ Q) = u ++ S ++ [B] ++ Q by simp,
        Chord.foldl_mvL (Chord.step flipL) (fun _ _ => rfl)]
    have hfB : ∀ x ∈ u ++ [B] ++ S ++ Q, x.1 < n := fun x hx => hfr x (by
      rw [ht₀]; simp at hx ⊢; tauto)
    refine ⟨E ++ mvL u.length S.length, fits_append_run hfE (Chord.fits_mvL _ _ (by
        rw [ht₀]; simp)), ?_, by rw [ncr_append, Chord.ncr_mvL], fun _ => ?_⟩
    · rw [hrun]
      have e : (u ++ [(n, B.2)] ++ S ++ Q).map (rl B.1 n) = (u ++ [B] ++ S ++ Q).map (rl B.1 n) := by
        simp [rl_of_ne (show (n, B.2).1 ≠ B.1 by simp; have := hfB B (by simp); omega),
          rl_of_eq (show B.1 = B.1 from rfl)]
      rw [show (n, B.2).1 = n from rfl, e]
      exact (Chord.iso_map_rl_of_fresh fun x hx => (hfB x hx).ne).symm
    · obtain ⟨p, hp⟩ := capBlk_cupAleft0 cs (wt D μ (Q.map Prod.snd)) (S.map Prod.snd) B.2
      refine XLt.of_smul p (xev_sgn_at (chordLay [] E) [] (u.map Prod.snd) (Q.map Prod.snd) hp
        (hchE.cast rfl (by simp)) ?_ (xChain_lmLc _ _) ?_ ?_)
      · have h1 := (xChain_xCupL B.2).whisk [] (S.map Prod.snd ++ [B.2])
        have h2 := (xChain_capBlk (S.map Prod.snd) B.2 0).whisk [B.2] []
        exact (h1.app h2 (by simp)).cast (by simp) (by simp)
      · simp
      · rw [hcE, ht₀, show u ++ (S ++ [B] ++ Q) = u ++ S ++ [B] ++ Q by simp,
          show u.length = (u.map Prod.snd).length by simp,
          show S.length = (S.map Prod.snd).length by simp]
        simp only [List.map_append, List.map_cons, List.map_nil]
        rw [chordLay_mvL]; simp
  · -- the cup creates `A` and the first strand of the block: a curl, lower
    subst hu' hS hv
    obtain rfl : (n, a) = A := h2
    have ha : flipL a = B.2 := by rw [← flipL_flipL B.2, ← hl]
    have hrun : run flipL (E ++ mvL u.length S'.length) = u ++ [B] ++ S' ++ Q := by
      rw [run_append_foldl, ht₀,
        show u ++ (S' ++ [B] ++ Q) = u ++ S' ++ [B] ++ Q by simp,
        Chord.foldl_mvL (Chord.step flipL) (fun _ _ => rfl)]
    have hfB : ∀ x ∈ u ++ [B] ++ S' ++ Q, x.1 < n := fun x hx => hfr x (by
      rw [ht₀]; simp at hx ⊢; tauto)
    refine ⟨E ++ mvL u.length S'.length, fits_append_run hfE (Chord.fits_mvL _ _ (by
        rw [ht₀]; simp)), ?_, by rw [ncr_append, Chord.ncr_mvL]; simp,
        fun h => absurd h (by rw [ncr_append, Chord.ncr_mvL]; simp)⟩
    rw [hrun]
    have e : (u ++ (n, flipL a) :: S' ++ Q).map (rl B.1 n) =
        (u ++ [B] ++ S' ++ Q).map (rl B.1 n) := by
      have hB' : rl B.1 n (n, B.2) = (n, B.2) :=
        rl_of_ne (show (n, B.2).1 ≠ B.1 by simp; have := hfB B (by simp); omega)
      simp [rl_of_eq (show B.1 = B.1 from rfl), ha, hB']
    rw [show (n, a).1 = n from rfl, e]
    exact (Chord.iso_map_rl_of_fresh fun x hx => (hfB x hx).ne).symm
  · -- the cup creates `A` and `B`: excluded
    exact absurd (by rw [← h2, ← h1]) hne
  · -- a cup inside the block: a double crossing, lower
    subst hS hu' hv
    have hAB : A.1 < n ∧ B.1 < n := ⟨hfr A (by rw [ht₀]; simp), hfr B (by rw [ht₀]; simp)⟩
    obtain ⟨E', hf', hiso, hle, -⟩ := ih P (S₁ ++ S₂) Q A B (by rw [ht₀]; simp) hl hne
    refine ⟨E' ++ [.cup (P.length + S₁.length) a], fits_snoc'.2 ⟨hf', by
        rw [hiso.length_eq]; show _ ≤ _; simp only [List.length_map, List.length_append]; omega⟩,
      iso_snoc_cup hf' hiso (f := rl B.1 A.1) (u := P ++ S₁) (w := S₂ ++ Q) (by lsimp) (by lsimp)
        (by simp) (rl_of_ne (by simp; omega)) (rl_of_ne (by simp; omega))
        (fresh_map_rl (fun x hx => hfr x (by rw [ht₀]; simp at hx ⊢; tauto)) hAB.1),
      by nomega, fun h => absurd h (by nomega)⟩
  · -- the cup creates `B` and the last strand of the block: a curl, lower
    subst hS hu' hv
    obtain rfl : (n, flipL a) = B := h1
    have ha : A.2 = a := by rw [hl, flipL_flipL]
    have hrun : run flipL (E ++ mvR P.length S'.length) = P ++ S' ++ [A] ++ w := by
      rw [run_append_foldl, ht₀,
        show P ++ [A] ++ S' ++ w = P ++ [A] ++ S' ++ w from rfl]
      have := Chord.foldl_mvR (Chord.step flipL) (fun _ _ => rfl) P S' w A
      simpa using this
    have hfA : ∀ x ∈ P ++ S' ++ w, x.1 ≠ n := fun x hx => (hfr x (by
      rw [ht₀]; simp at hx ⊢; tauto)).ne
    refine ⟨E ++ mvR P.length S'.length, fits_append_run hfE (Chord.fits_mvR _ _ (by
        rw [ht₀]; simp)), ?_, by rw [ncr_append, Chord.ncr_mvR]; simp,
        fun h => absurd h (by rw [ncr_append, Chord.ncr_mvR]; simp)⟩
    rw [hrun]
    have e : (P ++ (S' ++ [(n, a)]) ++ w).map (rl n A.1) = P ++ S' ++ [A] ++ w := by
      have h1 : P.map (rl n A.1) = P := Chord.map_rl_of_forall_ne fun x hx => hfA x (by simp [hx])
      have h2 : S'.map (rl n A.1) = S' :=
        Chord.map_rl_of_forall_ne fun x hx => hfA x (by simp [hx])
      have h3 : w.map (rl n A.1) = w := Chord.map_rl_of_forall_ne fun x hx => hfA x (by simp [hx])
      simp only [List.map_append, List.map_cons, List.map_nil, h1, h2, h3,
        rl_of_eq (show (n, a).1 = n from rfl)]
      rw [show (A.1, (n, a).2) = A by rw [← ha]]
      simp
    rw [show (n, flipL a).1 = n from rfl, e]
    exact Chord.Iso.refl _
  · -- the cup creates `B` and the strand to its right: a zigzag
    subst hu' hQ
    obtain rfl : (n, a) = B := h2
    have ha : A.2 = flipL a := hl
    have hrun : run flipL (E ++ mvR P.length S.length) = P ++ S ++ [A] ++ w := by
      rw [run_append_foldl, ht₀]
      have := Chord.foldl_mvR (Chord.step flipL) (fun _ _ => rfl) P S w A
      simpa using this
    have hfA : ∀ x ∈ P ++ S ++ w, x.1 ≠ n := fun x hx => (hfr x (by
      rw [ht₀]; simp at hx ⊢; tauto)).ne
    refine ⟨E ++ mvR P.length S.length, fits_append_run hfE (Chord.fits_mvR _ _ (by
        rw [ht₀]; simp)), ?_, by rw [ncr_append, Chord.ncr_mvR], fun _ => ?_⟩
    · rw [hrun]
      have e : (P ++ S ++ (n, flipL a) :: w).map (rl n A.1) = P ++ S ++ [A] ++ w := by
        have h1 : P.map (rl n A.1) = P :=
          Chord.map_rl_of_forall_ne fun x hx => hfA x (by simp [hx])
        have h2 : S.map (rl n A.1) = S :=
          Chord.map_rl_of_forall_ne fun x hx => hfA x (by simp [hx])
        have h3 : w.map (rl n A.1) = w :=
          Chord.map_rl_of_forall_ne fun x hx => hfA x (by simp [hx])
        simp only [List.map_append, List.map_cons, h1, h2, h3,
          rl_of_eq (show (n, flipL a).1 = n from rfl)]
        rw [show (A.1, (n, flipL a).2) = A by rw [← ha]]
        simp
      rw [show (n, a).1 = n from rfl, e]
      exact Chord.Iso.refl _
    · have hR : chordLay [] (E ++ mvR P.length S.length) = chordLay [] E ++
          (lmRc (flipL a) (S.map Prod.snd)).map (xwhL (P.map Prod.snd) (w.map Prod.snd)) := by
        rw [hcE, ht₀, show P.length = (P.map Prod.snd).length by simp,
          show S.length = (S.map Prod.snd).length by simp]
        simp only [List.map_append, List.map_cons, List.map_nil, ha]
        rw [← chordLay_mvR]
      rw [hR]
      rcases S.eq_nil_or_concat with hS | ⟨S₀, s₀, hS⟩
      · subst hS
        obtain ⟨p, hp⟩ := zigR cs (wt D μ (w.map Prod.snd)) a
        refine XLt.of_smul p (xev_sgn_at (chordLay [] E) [] (P.map Prod.snd) (w.map Prod.snd)
          (B := []) (hp.trans (by rw [xev_nil_eq_id])) (hchE.cast rfl (by simp [ha])) ?_ rfl ?_ ?_)
        · have h1 := (xChain_xCupL a).whisk [flipL a] []
          have h2 := (xChain_xCapL a).whisk [] [flipL a]
          exact (h1.app h2 (by simp)).cast (by simp) (by simp)
        · simp [capBlk_nil, ha]
        · simp [lmRc]
      · refine XLt.at (chordLay [] E) [] (P.map Prod.snd) (w.map Prod.snd)
          (capBlk_cupBright0 cs _ (S.map Prod.snd) a) (hchE.cast rfl (by simp [ha])) ?_
          (xChain_lmRc _ _) ?_ (by simp) ?_
        · have h1 := (xChain_xCupL a).whisk ([flipL a] ++ S.map Prod.snd) []
          have h2 := (xChain_capBlk (S.map Prod.snd) a 0).whisk [] [flipL a]
          exact (h1.app h2 (by simp)).cast (by simp) (by simp)
        · simp [ha]
        · subst hS; simp [hxE]
  · -- a cup to the right of the block
    subst hQ hu'
    have hAB : A.1 < n ∧ B.1 < n := ⟨hfr A (by rw [ht₀]; simp), hfr B (by rw [ht₀]; simp)⟩
    obtain ⟨E', hf', hiso, hle, hxl⟩ := ih P S (R ++ w) A B (by rw [ht₀]; simp) hl hne
    refine ⟨E' ++ [.cup (P.length + S.length + R.length) a], fits_snoc'.2 ⟨hf', by
        rw [hiso.length_eq]; show _ ≤ _; simp only [List.length_map, List.length_append]; omega⟩,
      iso_snoc_cup hf' hiso (f := rl B.1 A.1) (u := P ++ S ++ R) (w := w) (by lsimp) (by lsimp)
        (by simp; omega) (rl_of_ne (by simp; omega)) (rl_of_ne (by simp; omega))
        (fresh_map_rl (fun x hx => hfr x (by rw [ht₀]; simp at hx ⊢; tauto)) hAB.1),
      by nomega, fun h => ?_⟩
    have I := hxl (by nomega)
    have H := xlt_snoc (μ := μ) (n' := ncr E + S.length) hf' hiso (by simp)
      (hchE.app (xChain_blk (P := P) (S := S) (Q := R ++ w) hl) (by simp)) I
      (m := .cup (P.length + S.length + R.length) a) (show _ ≤ _ by simp; omega)
      (moveLay_cup_eq (u := (P ++ S ++ R).map Prod.snd) (w := w.map Prod.snd) a (by simp)
        (by simp; omega)) (by nomega) ((P ++ S ++ (R ++ [(n, a), (n, flipL a)] ++ w)).map Prod.snd)
    refine XLt.trans ?_ H
    refine XLt.symm (XLt.ichg (chordLay [] E) [] (P.map Prod.snd) (w.map Prod.snd)
      (xChain_capBlk (S.map Prod.snd) B.2 0)
      ((xChain_xCupL a).whisk (R.map Prod.snd) []) (hchE.cast rfl (by simp [hl])) ?_ ?_)
    · simp
    · simp [hl]

/-! ## The cap push -/

/-- **The cap push, keeping track of the pairing** (KL III, proof of Proposition 3.11): a cap
block on top of a chord diagram `E` is, up to sign modulo fewer crossings, a chord diagram whose
pairing is that of `E` with the two strands of the cap joined, with at most as many crossings. -/
theorem capPush (hR : R3Rel D Sc cs) (μ : X) :
    ∀ E : List (Move (Letter I)), Fits 0 E → CapPush cs μ E := by
  intro E
  induction E using List.reverseRecOn with
  | nil =>
    intro _ P S Q A B ht
    simp [Chord.run] at ht
  | append_singleton E m ih =>
    intro hf
    obtain ⟨hfE, hm⟩ := fits_snoc'.1 hf
    cases m with
    | cross p => exact capPush_cross hR (ih hfE) hfE hm
    | cup g a => exact capPush_cup (ih hfE) hfE hm a

end OddMath.SKM
