/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanChord
import OddMath.SKM.SpanBend

/-!
# The one-sided spanning set: canonical chord diagrams with dots, then bubbles

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 8.1
(spanning part), in the case of an empty bottom boundary, for the canonical choice of the reduced
matching of each pairing and of the distinguished point of each strand. The paper omits the proof
and refers to M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1,
proof of Proposition 3.11; the template is A. Lauda, arXiv:0803.3652v3, §8.

For a word `v` of letters of both orientations, every 2-morphism `1_μ → E_v 1_μ` is a linear
combination of the 2-morphisms
`chordLay [] (canon s) ++ dotsOn v is` followed by `bubAt μ v β`, where

* `canon s` is the canonical chord diagram (from `StringDiagrams.Chord`) of a pairing `s` of the
  letters of `v` (cups `η`, `η'` and crossings, `chordLay`),
* `dotsOn v is` places one dot on each strand at a position of `is`, and each such position is
  the left end of its arc (the distinguished point of the strand),
* `β` is a product of bubbles (`IsBubbleProd`), placed in the rightmost region.

The theorem is stated for the canonical choices only. For other choices, the ingredients are
here: a non-reducible chord diagram with the same pairing agrees with the canonical one up to sign
modulo diagrams with fewer crossings (`chordLay_normal_form`), and a dot moves along its arc up
to sign modulo lower terms and odd-bubble terms (`arc_dot`).

This is conditional on the three local relations `R3Rel`, `CapCurlRel` and `CupCurlRel`
(Reidemeister 3 in all orientations and the two curl relations modulo lower terms), which are
hypotheses here, as they are for the cap elimination `capElim'`.

Compared to the even case (Khovanov–Lauda), two things change:

* all moves hold only up to sign, by the super interchange law; this is enough for spanning;
* a dot moving around the leftward cup `η'` produces, for odd `i`, twice the odd bubble in the
  region below the cup ((4.4) of [BE2], `lemma41_eq4_one_odd`). The odd bubble is central: it
  slides through every strand exactly (`oddBubble_slide_up`, `oddBubble_slide_down`), so it moves
  to the rightmost region (`plcL_oddBubble`) and the term is the same diagram with one dot fewer,
  followed by an odd bubble. The spanning argument is therefore an induction on the number of
  dots.

## Main results

* `dot_move`, `dots_move`: dots pass a move of a chord diagram, up to sign modulo lower terms.
* `mv_to_chord`: a move diagram from `1_μ` is, up to sign modulo lower terms, a chord diagram
  followed by dots.
* `plcL_oddBubble`: an odd bubble in any region of `E_v 1_μ` is the odd bubble in the rightmost
  region.
* `dotCup`: a dot on the right leg of a cup is, up to sign, a dot on the left leg, plus (for the
  leftward cup and odd `i`) a multiple of the odd bubble below the cup.
* `arc_dot`: a dot slides along an arc of a canonical chord diagram, up to sign modulo lower terms
  and odd-bubble terms.
* `CanonSpan`, `mem_canonSpan_of_localRels`: the canonical diagrams with dots at the left ends of
  their arcs, followed by products of bubbles, span `Hom(1_μ, E_v 1_μ)`, given `R3Rel`,
  `CapCurlRel` and `CupCurlRel`.
* `canonDiagrams`, `diagBubSpan_canonDiagrams_eq_top`: the same in the form
  `diagBubSpan μ [] v (canonDiagrams v) = ⊤` of `SpanBend`, which bending extends to two-sided
  boundaries (`diagBubSpan_bendL_eq_top`).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation
open StringDiagrams.Chord (Move Step Rw Fits lstep canon run)

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} {cs : CScalars Sc}

/-! ## Composition with lower terms -/

section Comp

variable {ν : X} {s t r : List (Letter I)}

theorem ltL_comp_leL {n c : ℕ} {f : (pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)}
    {g : (pres D Sc).obj (ob D ν t) ⟶ (pres D Sc).obj (ob D ν r)}
    (hf : f ∈ LtL D Sc cs ν s t n) (hg : g ∈ LeL D Sc cs ν t r c) :
    f ≫ g ∈ LtL D Sc cs ν s r (n + c) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    exact leL_le_ltL (by omega) (leL_comp cs (xev_mem_leL cs le_rfl) hg)
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ a hx

theorem ltL_comp_xev {n : ℕ} {f : (pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)}
    (hf : f ∈ LtL D Sc cs ν s t n) (M : List (XLayer I)) :
    f ≫ xev cs ν t r M ∈ LtL D Sc cs ν s r (n + xcnt M) :=
  ltL_comp_leL hf (xev_mem_leL cs le_rfl)

theorem ltL_comp_bubAt {n : ℕ} {f : (pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)}
    (hf : f ∈ LtL D Sc cs ν s t n)
    {β : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν [])} (hβ : IsBubbleProd cs ν β) :
    f ≫ bubAt D Sc ν t β ∈ LtL D Sc cs ν s t n := by
  simpa using ltL_comp_leL hf (bubAt_mem_leL cs ν t hβ.mem_leL)

theorem XLt.append_right {n : ℕ} {L L' : List (XLayer I)} (h : XLt cs ν s r n L L')
    (hL : XChain s L r) (hL' : XChain s L' r) (M : List (XLayer I)) :
    XLt cs ν s t (n + xcnt M) (L ++ M) (L' ++ M) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p, ?_⟩
  rw [xev_append cs M hL, xev_append cs M hL', ← Linear.smul_comp, ← Preadditive.sub_comp]
  exact ltL_comp_xev hp M

end Comp

/-! ## Dots -/

section Dots

/-- A dot on the strand at position `i` of the letters `t` (no layer if `i` is out of range). -/
def dotOn (t : List (Letter I)) (i : ℕ) : List (XLayer I) :=
  match t.drop i with
  | l :: w => (xDotL l).map (xwhL (t.take i) w)
  | [] => []

/-- Dots on the strands at the positions `is` (from the bottom). -/
def dotsOn (t : List (Letter I)) (is : List ℕ) : List (XLayer I) := (is.map (dotOn t)).flatten

/-- The new position of the strand at position `i` after a move. -/
def movePos : Move (Letter I) → ℕ → ℕ
  | .cup g _, i => if i < g then i else i + 2
  | .cross p, i => Chord.tau p i

@[simp] theorem dotOn_eq (u w : List (Letter I)) (l : Letter I) :
    dotOn (u ++ l :: w) u.length = (xDotL l).map (xwhL u w) := by
  simp [dotOn]

theorem dotOn_eq' {t u w : List (Letter I)} {l : Letter I} {i : ℕ} (ht : t = u ++ l :: w)
    (hi : i = u.length) : dotOn t i = (xDotL l).map (xwhL u w) := by
  subst ht hi; exact dotOn_eq u w l

theorem exists_split_dot {t : List (Letter I)} {i : ℕ} (h : i < t.length) :
    ∃ u l w, t = u ++ l :: w ∧ u.length = i := by
  obtain ⟨u, w', rfl, hu⟩ := exists_split_cup (l := t) (g := i) h.le
  match w', h with
  | l :: w, _ => exact ⟨u, l, w, rfl, hu⟩
  | [], h => simp at h; omega

theorem xChain_dotOn {t : List (Letter I)} {i : ℕ} (h : i < t.length) :
    XChain t (dotOn t i) t := by
  obtain ⟨u, l, w, rfl, rfl⟩ := exists_split_dot h
  rw [dotOn_eq]; simpa using (xChain_xDotL l).whisk u w

@[simp] theorem xcnt_dotOn (t : List (Letter I)) (i : ℕ) : xcnt (dotOn t i) = 0 := by
  unfold dotOn; split <;> simp

@[simp] theorem dotsOn_nil (t : List (Letter I)) : dotsOn t [] = [] := rfl

@[simp] theorem dotsOn_cons (t : List (Letter I)) (i : ℕ) (is : List ℕ) :
    dotsOn t (i :: is) = dotOn t i ++ dotsOn t is := rfl

theorem dotsOn_append (t : List (Letter I)) (is js : List ℕ) :
    dotsOn t (is ++ js) = dotsOn t is ++ dotsOn t js := by
  simp [dotsOn]

@[simp] theorem xcnt_dotsOn (t : List (Letter I)) (is : List ℕ) : xcnt (dotsOn t is) = 0 := by
  induction is with
  | nil => rfl
  | cons i is ih => rw [dotsOn_cons, xcnt_append, xcnt_dotOn, ih]

theorem xChain_dotsOn {t : List (Letter I)} : ∀ {is : List ℕ}, (∀ i ∈ is, i < t.length) →
    XChain t (dotsOn t is) t
  | [], _ => rfl
  | i :: _, h => (xChain_dotOn (h i List.mem_cons_self)).append
      (xChain_dotsOn fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- **A dot passes a move** (exactly up to sign for a cup or a crossing of other strands, up to
sign modulo diagrams with fewer crossings if the dot is on a strand of the crossing). -/
theorem dot_move {t : List (Letter I)} {m : Move (Letter I)} (hm : m.Ok t.length) {i : ℕ}
    (hi : i < t.length) {ν : X} {s₀ t₀ : List (Letter I)} (P Q : List (XLayer I))
    (hP : XChain s₀ P t) :
    XLt cs ν s₀ t₀ (xcnt P + ncr [m] + xcnt Q) (P ++ dotOn t i ++ moveLay t m ++ Q)
      (P ++ moveLay t m ++ dotOn (chStep t m) (movePos m i) ++ Q) := by
  cases m with
  | cup g a =>
    simp only [Chord.Move.Ok] at hm
    obtain ⟨u, w, rfl, rfl⟩ := exists_split_cup (l := t) hm
    rw [moveLay_cup, chStep_cup]
    simp only [movePos]
    split_ifs with hig
    · obtain ⟨u1, l, M, rfl, rfl⟩ := exists_split_dot (t := u) hig
      rw [dotOn_eq' (u := u1) (l := l) (w := M ++ w) (by simp) rfl,
        dotOn_eq' (u := u1) (l := l) (w := M ++ a :: flipL a :: w) (by simp) rfl]
      have hB : XChain M ((xCupL a).map (xwhL M [])) (M ++ [a, flipL a]) := by
        simpa using (xChain_xCupL a).whisk M []
      exact XLt.ichg P Q u1 w (xChain_xDotL l) hB (hP.cast rfl (by simp)) (by simp) (by simp)
    · obtain ⟨M, l, w1, rfl, hM⟩ := exists_split_dot (t := w) (i := i - u.length)
        (by simp at hi; omega)
      rw [dotOn_eq' (u := u ++ M) (l := l) (w := w1) (by simp) (by simp; omega),
        dotOn_eq' (u := u ++ a :: flipL a :: M) (l := l) (w := w1) (by simp) (by simp; omega)]
      have hB : XChain (M ++ [l]) ((xDotL l).map (xwhL M [])) (M ++ [l]) := by
        simpa using (xChain_xDotL l).whisk M []
      exact (XLt.ichg P Q u w1 (xChain_xCupL a) hB (hP.cast rfl (by simp)) (by simp)
        (by simp)).symm
  | cross p =>
    simp only [Chord.Move.Ok] at hm
    obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := t) hm
    rw [moveLay_cross, chStep_cross]
    simp only [movePos]
    rcases (show i < u.length ∨ i = u.length ∨ i = u.length + 1 ∨ u.length + 1 < i by omega) with
      h | rfl | rfl | h
    · obtain ⟨u1, l, M, rfl, rfl⟩ := exists_split_dot (t := u) h
      rw [Chord.tau_of_ne (by simp) (by simp; omega),
        dotOn_eq' (u := u1) (l := l) (w := M ++ x :: y :: w) (by simp) rfl,
        dotOn_eq' (u := u1) (l := l) (w := M ++ y :: x :: w) (by simp) rfl]
      have hB : XChain (M ++ [x, y]) ((xCrL x y).map (xwhL M [])) (M ++ [y, x]) := by
        simpa using (xChain_xCrL x y).whisk M []
      exact XLt.ichg P Q u1 w (xChain_xDotL l) hB (hP.cast rfl (by simp)) (by simp) (by simp)
    · rw [Chord.tau_left, dotOn_eq' (u := u) (l := x) (w := y :: w) rfl rfl,
        dotOn_eq' (u := u ++ [y]) (l := x) (w := w) (by simp) (by simp)]
      refine XLt.at P Q u w (ds_left cs _ x y) (hP.cast rfl (by simp)) ?_ ?_ (by simp) (by simp)
        (by simp [ncr])
      · exact ((xChain_xDotL x).whisk [] [y]).app (xChain_xCrL x y) (by simp) |>.cast rfl rfl
      · exact (xChain_xCrL x y).app ((xChain_xDotL x).whisk [y] []) (by simp) |>.cast rfl
          (by simp)
    · rw [Chord.tau_right, dotOn_eq' (u := u ++ [x]) (l := y) (w := w) (by simp) (by simp),
        dotOn_eq' (u := u) (l := y) (w := x :: w) rfl rfl]
      refine XLt.at P Q u w (ds_right cs _ x y) (hP.cast rfl (by simp)) ?_ ?_ (by simp)
        (by simp) (by simp [ncr])
      · exact ((xChain_xDotL y).whisk [x] []).app (xChain_xCrL x y) (by simp) |>.cast
          (by simp) rfl
      · exact (xChain_xCrL x y).app ((xChain_xDotL y).whisk [] [x]) (by simp) |>.cast rfl
          (by simp)
    · obtain ⟨M, l, w1, rfl, hM⟩ := exists_split_dot (t := w) (i := i - u.length - 2)
        (by simp at hi; omega)
      rw [Chord.tau_of_ne (by omega) (by omega),
        dotOn_eq' (u := u ++ x :: y :: M) (l := l) (w := w1) (by simp) (by simp; omega),
        dotOn_eq' (u := u ++ y :: x :: M) (l := l) (w := w1) (by simp) (by simp; omega)]
      have hB : XChain (M ++ [l]) ((xDotL l).map (xwhL M [])) (M ++ [l]) := by
        simpa using (xChain_xDotL l).whisk M []
      exact (XLt.ichg P Q u w1 (xChain_xCrL x y) hB (hP.cast rfl (by simp)) (by simp)
        (by simp)).symm

/-- **Dots pass a move.** -/
theorem dots_move {t : List (Letter I)} {m : Move (Letter I)} (hm : m.Ok t.length) :
    ∀ {is : List ℕ}, (∀ i ∈ is, i < t.length) → ∀ {ν : X} {s₀ t₀ : List (Letter I)}
      (P Q : List (XLayer I)), XChain s₀ P t →
    XLt cs ν s₀ t₀ (xcnt P + ncr [m] + xcnt Q) (P ++ dotsOn t is ++ moveLay t m ++ Q)
      (P ++ moveLay t m ++ dotsOn (chStep t m) (is.map (movePos m)) ++ Q)
  | [], _, _, _, _, P, Q, _ => by
    simp only [dotsOn_nil, List.map_nil, List.append_nil]; exact XLt.refl _
  | i :: is, h, ν, s₀, t₀, P, Q, hP => by
    have hi := h i List.mem_cons_self
    have h1 := dots_move hm (fun j hj => h j (List.mem_cons_of_mem _ hj)) (ν := ν) (t₀ := t₀)
      (P ++ dotOn t i) Q (hP.append (xChain_dotOn hi))
    have h2 := dot_move (cs := cs) (ν := ν) (t₀ := t₀) hm hi P
      (dotsOn (chStep t m) (is.map (movePos m)) ++ Q) hP
    simp only [xcnt_append, xcnt_dotOn, xcnt_dotsOn, add_zero, zero_add] at h1 h2
    simp only [dotsOn_cons, List.map_cons, List.append_assoc] at h1 h2 ⊢
    exact h1.trans h2

/-- **Move diagrams as chord diagrams with dots on top**: a move diagram from `1_μ` (dots, cups
and crossings) is, up to sign modulo diagrams with fewer crossings, a chord diagram followed by
dots on its top strands. -/
theorem mv_to_chord (μ : X) : ∀ (ms : List (Mv I)) {v : List (Letter I)}, MvChain [] ms v →
    ∃ (E : List (Move (Letter I))) (is : List ℕ), Fits 0 E ∧ E.foldl chStep [] = v ∧
      ncr E = xcnt (mvLay ms) ∧ (∀ i ∈ is, i < v.length) ∧
      XLt cs μ [] v (xcnt (mvLay ms)) (mvLay ms) (chordLay [] E ++ dotsOn v is) := by
  intro ms
  induction ms using List.reverseRecOn with
  | nil =>
    intro v h
    have hv : [] = v := h
    subst hv
    exact ⟨[], [], trivial, rfl, rfl, by simp, XLt.refl _⟩
  | append_singleton ms m ih =>
    intro v h
    obtain ⟨h1, h2⟩ := MvChain.of_snoc h
    obtain ⟨E, is, hE, hlet, hn, his, hdiff⟩ := ih h1
    have hA : XChain [] (mvLay ms) m.src := h1.xChain
    have hB : XChain [] (chordLay [] E ++ dotsOn m.src is) m.src := by
      have := xChain_chordLay (l := []) hE
      rw [hlet] at this
      exact this.append (xChain_dotsOn his)
    have Δ1 := hdiff.append_right (t := v) hA hB m.lay
    rw [mvLay_append, mvLay_singleton, xcnt_append]
    subst h2
    cases m with
    | dot u l w =>
      refine ⟨E, is ++ [u.length], hE, hlet, by rw [hn, Mv.xcnt_lay]; simp [Mv.loc], ?_, ?_⟩
      · intro i hi
        rcases List.mem_append.1 hi with hi | hi
        · have := his i hi; simpa [Mv.src, Mv.tgt, Mv.lsrc, Mv.ltgt, Mv.pre, Mv.post] using this
        · simp at hi; simp [Mv.tgt, Mv.ltgt, Mv.pre, Mv.post, hi]
      · have e : chordLay [] E ++ dotsOn (Mv.dot u l w).tgt (is ++ [u.length]) =
            chordLay [] E ++ dotsOn (Mv.dot u l w).src is ++ (Mv.dot u l w).lay := by
          simp only [Mv.tgt, Mv.src, Mv.lay, Mv.loc, Mv.pre, Mv.post, Mv.lsrc, Mv.ltgt,
            dotsOn_append, dotsOn_cons, dotsOn_nil, List.append_nil, List.append_assoc]
          congr 2
          exact dotOn_eq' (by simp) rfl
        rw [e]; exact Δ1
    | cup u a w =>
      have hlay : (Mv.cup u a w).lay = moveLay (u ++ w) (.cup u.length a) := by
        rw [moveLay_cup]; rfl
      have hsrc : (Mv.cup u a w).src = u ++ w := by simp [Mv.src, Mv.lsrc, Mv.pre, Mv.post]
      have htgt : (Mv.cup u a w).tgt = chStep (u ++ w) (.cup u.length a) := by
        rw [chStep_cup]; simp [Mv.tgt, Mv.ltgt, Mv.pre, Mv.post]
      rw [hsrc] at hlet his Δ1 hB
      rw [hlay, htgt] at Δ1 ⊢
      have hm : (Move.cup u.length a : Move (Letter I)).Ok (u ++ w).length := by
        simp [Chord.Move.Ok]
      refine ⟨E ++ [.cup u.length a], is.map (movePos (.cup u.length a)), ?_, ?_, ?_, ?_, ?_⟩
      · rw [Chord.fits_append]
        refine ⟨hE, ?_, trivial⟩
        rw [show (0 : ℕ) = ([] : List (Letter I)).length from rfl, foldl_len_eq, hlet]
        exact hm
      · rw [List.foldl_append, hlet]; rfl
      · rw [ncr_append, hn, xcnt_moveLay hm]
      · intro j hj
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
        have := his i hi
        rw [chStep_cup]
        simp only [movePos, List.length_append, List.length_cons] at this ⊢
        split_ifs <;> omega
      · have Δ2 := dots_move (cs := cs) (ν := μ) (t₀ := chStep (u ++ w) (.cup u.length a)) hm his
          (chordLay [] E) [] (by simpa [hlet] using xChain_chordLay (l := []) hE)
        rw [xcnt_chordLay (l := []) hE, xcnt_nil, add_zero] at Δ2
        rw [xcnt_moveLay hm]
        rw [xcnt_moveLay hm] at Δ1
        rw [chordLay_append, hlet]
        simp only [chordLay, List.append_nil] at Δ2 ⊢
        exact Δ1.trans (Δ2.mono (by simp [hn]))
    | cross u x y w =>
      have hlay : (Mv.cross u x y w).lay = moveLay (u ++ x :: y :: w) (.cross u.length) := by
        rw [moveLay_cross]; rfl
      have hsrc : (Mv.cross u x y w).src = u ++ x :: y :: w := by
        simp [Mv.src, Mv.lsrc, Mv.pre, Mv.post]
      have htgt : (Mv.cross u x y w).tgt = chStep (u ++ x :: y :: w) (.cross u.length) := by
        rw [chStep_cross]; simp [Mv.tgt, Mv.ltgt, Mv.pre, Mv.post]
      rw [hsrc] at hlet his Δ1 hB
      rw [hlay, htgt] at Δ1 ⊢
      have hm : (Move.cross u.length : Move (Letter I)).Ok (u ++ x :: y :: w).length := by
        simp [Chord.Move.Ok]
      refine ⟨E ++ [.cross u.length], is.map (movePos (I := I) (.cross u.length)), ?_, ?_, ?_, ?_, ?_⟩
      · rw [Chord.fits_append]
        refine ⟨hE, ?_, trivial⟩
        rw [show (0 : ℕ) = ([] : List (Letter I)).length from rfl, foldl_len_eq, hlet]
        exact hm
      · rw [List.foldl_append, hlet]; rfl
      · rw [ncr_append, hn, xcnt_moveLay hm]
      · intro j hj
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
        have := his i hi
        rw [chStep_cross]
        simp only [movePos, List.length_append, List.length_cons] at this ⊢
        unfold Chord.tau; split_ifs <;> omega
      · have Δ2 := dots_move (cs := cs) (ν := μ) (t₀ := chStep (u ++ x :: y :: w) (.cross u.length))
          hm his (chordLay [] E) [] (by simpa [hlet] using xChain_chordLay (l := []) hE)
        rw [xcnt_chordLay (l := []) hE, xcnt_nil, add_zero] at Δ2
        rw [xcnt_moveLay hm]
        rw [xcnt_moveLay hm] at Δ1
        rw [chordLay_append, hlet]
        simp only [chordLay, List.append_nil] at Δ2 ⊢
        exact Δ1.trans (Δ2.mono (by rw [hn]))

end Dots

/-! ## Odd bubbles move to the rightmost region -/

section OddBubble

theorem wordCast_wordCast (μ : X) {s t s' t' s'' t'' : List (Letter I)} (h₁ : s = s')
    (h₁' : t = t') (h₂ : s' = s'') (h₂' : t' = t'')
    (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    wordCast μ h₂ h₂' (wordCast μ h₁ h₁' f) = wordCast μ (h₁.trans h₂) (h₁'.trans h₂') f := by
  subst h₁ h₁' h₂ h₂'; rfl

theorem wordCast_self (μ : X) {s t : List (Letter I)} (h : s = s) (h' : t = t)
    (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) : wordCast μ h h' f = f := rfl

theorem plcL_congr_left (μ : X) {P P' : List (Letter I)} (h : P = P') (Q s t : List (Letter I))
    (f : (pres D Sc).obj (ob D (wt D μ Q) s) ⟶ (pres D Sc).obj (ob D (wt D μ Q) t)) :
    plcL D Sc μ P' Q s t f = wordCast μ (by rw [h]) (by rw [h]) (plcL D Sc μ P Q s t f) := by
  subst h; rfl

theorem bubAt_congr (μ : X) {v v' : List (Letter I)} (h : v = v')
    (β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])) :
    bubAt D Sc μ v' β = wordCast μ h h (bubAt D Sc μ v β) := by
  subst h; rfl

theorem plcL_nil_eq_bubAt (μ : X) (P : List (Letter I))
    (f : (pres D Sc).obj (ob D (wt D μ []) []) ⟶ (pres D Sc).obj (ob D (wt D μ []) [])) :
    plcL D Sc μ P [] [] [] f = bubAt D Sc μ (P ++ [] ++ []) f := by
  have e := plcL_congr_left μ (show P = P ++ [] ++ [] by simp) [] [] [] f
  dsimp only [bubAt, LinearMap.comp_apply]
  erw [e, wordCast_wordCast, wordCast_self]

/-- **An odd bubble in any region is the odd bubble in the rightmost region** (the odd bubbles are
central, [BE2] Corollary 7.4: they slide exactly through upward and downward strands). -/
theorem plcL_oddBubble {i : I} (hi : D.parity i = 1) (μ : X) : ∀ (Q P : List (Letter I)),
    plcL D Sc μ P Q [] [] (oddBubble cs i (wt D μ Q)) =
      bubAt D Sc μ (P ++ [] ++ Q) (oddBubble cs i μ)
  | [], P => plcL_nil_eq_bubAt μ P _
  | l :: Q, P => by
    have hs : plcL D Sc (wt D μ Q) [] [l] [] [] (oddBubble cs i (wt D μ (l :: Q))) =
        plcL D Sc (wt D μ Q) [l] [] [] [] (oddBubble cs i (wt D μ Q)) := by
      obtain ⟨_ | _, j⟩ := l
      · exact oddBubble_slide_down cs i j _ hi
      · exact (oddBubble_slide_up cs i j _ hi).symm
    have e1 := plcL_plcL_left μ P Q l (oddBubble cs i (wt D μ (l :: Q)))
    rw [hs, plcL_plcL_right, plcL_oddBubble hi μ Q (P ++ [l])] at e1
    have e2 := congrArg (wordCast μ (show P ++ [l] ++ Q = P ++ [] ++ l :: Q by simp)
      (show P ++ [l] ++ Q = P ++ [] ++ l :: Q by simp)) e1
    rw [wordCast_wordCast, wordCast_wordCast, wordCast_self] at e2
    rw [← e2, bubAt_congr μ (show P ++ [l] ++ [] ++ Q = P ++ [] ++ l :: Q by simp)]

/-- **A local relation with an odd-bubble term, in context**: the odd bubble below the local piece
`C` moves to the rightmost region at the top. -/
theorem xev_oddBubble_ctx {i : I} (μ : X) {s₀ t₀ : List (Letter I)}
    (pre post : List (XLayer I)) (u v : List (Letter I)) {t : List (Letter I)}
    {A B C : List (XLayer I)} {p : ZMod 2} {r : k}
    (E : xev cs (wt D μ v) [] t A = zsign k p • xev cs (wt D μ v) [] t B +
      r • (oddBubble cs i (wt D μ v) ≫ xev cs (wt D μ v) [] t C))
    (hir : D.parity i = 1 ∨ r = 0)
    (hpre : XChain s₀ pre (u ++ [] ++ v)) (hA : XChain [] A t) (hB : XChain [] B t)
    (hC : XChain [] C t) :
    ∃ q : ZMod 2, xev cs μ s₀ t₀ (pre ++ A.map (xwhL u v) ++ post) =
      zsign k p • xev cs μ s₀ t₀ (pre ++ B.map (xwhL u v) ++ post) +
        (zsign k q * r) • (xev cs μ s₀ t₀ (pre ++ C.map (xwhL u v) ++ post) ≫
          bubAt D Sc μ t₀ (oddBubble cs i μ)) := by
  rcases hir with hi | rfl
  · obtain ⟨q, hq⟩ := bubAt_comp_xev cs (μ := μ) (s := u ++ [] ++ v) (t := t₀)
      (C.map (xwhL u v) ++ post) (IsBubbleProd.of_oddBubble μ i)
    have hC' : plcL D Sc μ u v [] t (xev cs (wt D μ v) [] t C) ≫
        xev cs μ (u ++ t ++ v) t₀ post =
          xev cs μ (u ++ [] ++ v) t₀ (C.map (xwhL u v) ++ post) := by
      rw [xev_append cs _ (hC.whisk u v), plcL_xev]
    have hfull : xev cs μ s₀ (u ++ [] ++ v) pre ≫
        xev cs μ (u ++ [] ++ v) t₀ (C.map (xwhL u v) ++ post) =
          xev cs μ s₀ t₀ (pre ++ C.map (xwhL u v) ++ post) := by
      rw [← xev_append cs _ hpre, List.append_assoc]
    refine ⟨q, ?_⟩
    rw [xev_ctx cs μ pre post u v hpre hA, xev_ctx cs μ pre post u v hpre hB, E, map_add,
      map_smul, map_smul, plcL_comp, plcL_oddBubble hi]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul,
      Category.assoc]
    rw [hC', hq, Linear.comp_smul, ← Category.assoc (xev cs μ s₀ (u ++ [] ++ v) pre)
      (xev cs μ (u ++ [] ++ v) t₀ _), hfull, smul_smul, mul_comm]
  · refine ⟨0, ?_⟩
    rw [xev_ctx cs μ pre post u v hpre hA, xev_ctx cs μ pre post u v hpre hB, E]
    simp only [zero_smul, add_zero, mul_zero, map_smul, Linear.smul_comp, Linear.comp_smul]

/-- **A dot moves around a cup** ((2.3), Proposition 4.1 (4.4)): a dot on the right leg of the
cup `xCupL x` is, up to sign, a dot on its left leg, plus (for the leftward cup `η'` and odd `i`)
a multiple of the odd bubble (2.18) below the cup. -/
theorem dotCup (ν : X) (x : Letter I) : ∃ (p : ZMod 2) (r : k), (D.parity x.2 = 1 ∨ r = 0) ∧
    xev cs ν [] [x, flipL x] (xCupL x ++ (xDotL (flipL x)).map (xwhL [x] [])) =
      zsign k p • xev cs ν [] [x, flipL x] (xCupL x ++ (xDotL x).map (xwhL [] [flipL x])) +
        r • (oddBubble cs x.2 ν ≫ xev cs ν [] [x, flipL x] (xCupL x)) := by
  obtain ⟨_ | _, i⟩ := x
  · refine ⟨D.parity i * ((1 / 2 : ℕ) : ZMod 2), 0, Or.inr rfl, ?_⟩
    rw [zero_smul, add_zero]
    have E := eq_2_3_a Sc i ν 1
    rw [← xev_map_ofL cs, ← xev_map_ofL cs, ddotsL_one'] at E
    exact E
  · have hL : xev cs ν [] [up i, dn i] (xCupL (up i) ++ (xDotL (dn i)).map (xwhL [up i] [])) =
        etaP cs i ν ≫ dRM D Sc i ν := by
      rw [xev_append cs _ (show XChain [] (xCupL (up i)) [up i, dn i] from xChain_xCupL (up i)),
        xCupL_up, xev_lcup, xDotL_dn, map_xwhL_map_ofL,
        xev_map_ofL]
    have hR : xev cs ν [] [up i, dn i] (xCupL (up i) ++ (xDotL (up i)).map (xwhL [] [dn i])) =
        etaP cs i ν ≫ uLM D Sc i ν := by
      rw [xev_append cs _ (show XChain [] (xCupL (up i)) [up i, dn i] from xChain_xCupL (up i)),
        xCupL_up, xev_lcup,
        show (xDotL (up i)).map (xwhL [] [dn i]) = (dotsL [] i [dn i] 1).map ofL from rfl,
        xev_map_ofL]
    have hC : xev cs ν [] [up i, dn i] (xCupL (up i)) = etaP cs i ν := by
      rw [xCupL_up, xev_lcup]
    show ∃ (p : ZMod 2) (r : k), (D.parity i = 1 ∨ r = 0) ∧
      xev cs ν [] [up i, dn i] (xCupL (up i) ++ (xDotL (dn i)).map (xwhL [up i] [])) =
        zsign k p • xev cs ν [] [up i, dn i] (xCupL (up i) ++ (xDotL (up i)).map (xwhL [] [dn i])) +
          r • (oddBubble cs i ν ≫ xev cs ν [] [up i, dn i] (xCupL (up i)))
    rw [hL, hR, hC]
    rcases zmod2_cases (D.parity i) with hi | hi
    · exact ⟨0, 0, Or.inr rfl, by rw [lemma41_eq4_one_even cs i ν hi, zsign_zero, one_smul,
        zero_smul, add_zero]⟩
    · refine ⟨(D.h i ν : ZMod 2), -(zsign k (D.h i ν : ZMod 2) * 2), Or.inl hi, ?_⟩
      rw [lemma41_eq4_one_odd cs i ν hi, smul_add, smul_smul, zsign_mul_self', one_smul,
        smul_smul]
      module

end OddBubble

/-! ## Equality up to sign modulo a submodule -/

section SignRel

variable {M : Type*} [AddCommGroup M] [Module k M]

/-- `a` and `b` agree up to sign modulo the submodule `S`. -/
def SignRel (S : Submodule k M) (a b : M) : Prop := ∃ p : ZMod 2, a - zsign k p • b ∈ S

namespace SignRel

variable {S S' : Submodule k M} {a b c : M}

theorem refl (a : M) : SignRel S a a :=
  ⟨0, by rw [zsign_zero, one_smul, sub_self]; exact Submodule.zero_mem _⟩

theorem symm (h : SignRel S a b) : SignRel S b a := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p, ?_⟩
  have e : b - zsign k p • a = (-zsign k p) • (a - zsign k p • b) := by
    rw [smul_sub, smul_smul, neg_mul, zsign_mul_self', neg_smul, neg_smul, one_smul]; abel
  rw [e]; exact Submodule.smul_mem _ _ hp

theorem trans (h₁ : SignRel S a b) (h₂ : SignRel S b c) : SignRel S a c := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  refine ⟨p + q, ?_⟩
  have := Submodule.add_mem _ hp (Submodule.smul_mem _ (zsign k p) hq)
  rwa [smul_sub, smul_smul, ← zsign_add, sub_add_sub_cancel] at this

theorem mono (h : SignRel S a b) (hS : S ≤ S') : SignRel S' a b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hS hp⟩

theorem low (h : SignRel S a b) (hb : b ∈ S) : a ∈ S := by
  obtain ⟨p, hp⟩ := h
  have := Submodule.add_mem _ hp (Submodule.smul_mem _ (zsign k p) hb)
  rwa [sub_add_cancel] at this

end SignRel

end SignRel

theorem XLt.signRel {ν : X} {s t : List (Letter I)} {n : ℕ} {L L' : List (XLayer I)}
    (h : XLt cs ν s t n L L') : SignRel (LtL D Sc cs ν s t n) (xev cs ν s t L) (xev cs ν s t L') :=
  h

variable (cs) in
/-- The extended diagram `L` followed by products of bubbles in the rightmost region. -/
def BubTerm (ν : X) (s t : List (Letter I)) (L : List (XLayer I)) :
    Submodule k ((pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)) :=
  Submodule.span k {f | ∃ β, IsBubbleProd cs ν β ∧ f = xev cs ν s t L ≫ bubAt D Sc ν t β}

/-! ## Dots on distinct strands commute up to sign -/

section DotComm

theorem dotOn_comm_lt {t : List (Letter I)} {i j : ℕ} (hij : i < j) (hj : j < t.length)
    {ν : X} {s₀ t₀ : List (Letter I)} {n : ℕ} (P Q : List (XLayer I)) (hP : XChain s₀ P t) :
    XLt cs ν s₀ t₀ n (P ++ dotOn t i ++ dotOn t j ++ Q) (P ++ dotOn t j ++ dotOn t i ++ Q) := by
  obtain ⟨u, l, w, rfl, rfl⟩ := exists_split_dot (t := t) (i := i) (by omega)
  obtain ⟨M, l', w', rfl, hM⟩ := exists_split_dot (t := w) (i := j - u.length - 1)
    (by simp at hj; omega)
  rw [dotOn_eq, dotOn_eq' (u := u ++ l :: M) (l := l') (w := w') (by simp) (by simp; omega)]
  have hB : XChain (M ++ [l']) ((xDotL l').map (xwhL M [])) (M ++ [l']) := by
    simpa using (xChain_xDotL l').whisk M []
  exact XLt.ichg P Q u w' (xChain_xDotL l) hB (hP.cast rfl (by simp)) (by simp) (by simp)

theorem dotOn_comm {t : List (Letter I)} {i j : ℕ} (hi : i < t.length) (hj : j < t.length)
    {ν : X} {s₀ t₀ : List (Letter I)} {n : ℕ} (P Q : List (XLayer I)) (hP : XChain s₀ P t) :
    XLt cs ν s₀ t₀ n (P ++ dotOn t i ++ dotOn t j ++ Q) (P ++ dotOn t j ++ dotOn t i ++ Q) := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact dotOn_comm_lt h hj P Q hP
  · exact XLt.refl _
  · exact (dotOn_comm_lt h hi P Q hP).symm

/-- **Dots on distinct strands commute up to sign.** -/
theorem dotsOn_perm {t : List (Letter I)} {is js : List ℕ} (h : is.Perm js) :
    (∀ i ∈ is, i < t.length) → ∀ {ν : X} {s₀ t₀ : List (Letter I)} {n : ℕ}
      (P Q : List (XLayer I)), XChain s₀ P t →
    XLt cs ν s₀ t₀ n (P ++ dotsOn t is ++ Q) (P ++ dotsOn t js ++ Q) := by
  induction h with
  | nil => intros; exact XLt.refl _
  | cons x h ih =>
    intro hb ν s₀ t₀ n P Q hP
    simp only [dotsOn_cons, ← List.append_assoc]
    exact ih (fun i hi => hb i (List.mem_cons_of_mem _ hi)) _ Q
      (hP.append (xChain_dotOn (hb x List.mem_cons_self)))
  | swap x y l =>
    intro hb ν s₀ t₀ n P Q hP
    simp only [dotsOn_cons]
    have := dotOn_comm (cs := cs) (ν := ν) (t₀ := t₀) (n := n) (t := t) (hb y List.mem_cons_self)
      (hb x (List.mem_cons_of_mem _ List.mem_cons_self)) P (dotsOn t l ++ Q) hP
    simpa [List.append_assoc] using this
  | trans h1 h2 ih1 ih2 =>
    intro hb ν s₀ t₀ n P Q hP
    exact (ih1 hb P Q hP).trans (ih2 (fun i hi => hb i (h1.symm.subset hi)) P Q hP)

end DotComm

/-! ## Dots slide along the arcs of the canonical diagrams -/

section Arcs

open StringDiagrams.Chord (Same Valid Lettered Iso)

theorem canon_letters {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered flipL s) :
    Fits 0 (canon s) ∧ (canon s).foldl chStep [] = s.map Prod.snd := by
  obtain ⟨hf, hiso⟩ := Chord.run_canon (d := flipL) _ (Nat.lt_succ_self _) hv hl
  refine ⟨hf, ?_⟩
  rw [← hiso.1, Chord.snd_run]

theorem xChain_chordLay_canon {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered flipL s) :
    XChain [] (chordLay [] (canon s)) (s.map Prod.snd) := by
  have := xChain_chordLay (l := []) (canon_letters hv hl).1
  rwa [(canon_letters hv hl).2] at this

theorem snd_adj {s : List (ℕ × Letter I)} (hl : Lettered flipL s) {r : ℕ}
    (hr : Same s r (r + 1)) :
    (s[r + 1]'hr.lt_right).2 = flipL (s[r]'hr.lt_left).2 := by
  have := hl r (r + 1) hr (by omega)
  rw [List.getElem?_eq_getElem hr.lt_left, List.getElem?_eq_getElem hr.lt_right] at this
  simpa using this

theorem map_snd_adj {s : List (ℕ × Letter I)} (hl : Lettered flipL s) {r : ℕ}
    (hr : Same s r (r + 1)) :
    s.map Prod.snd = chStep ((Chord.rmAt s r).map Prod.snd) (.cup r (s[r]'hr.lt_left).2) := by
  have e := Chord.insAt_rmAt s (show r + 1 < s.length from hr.lt_right)
  conv_lhs => rw [← e]
  rw [Chord.map_insAt, snd_adj hl hr]
  rfl

/-- **A dot slides along an arc of the canonical diagram** (from one end to the other), up to sign
modulo diagrams with fewer crossings and the same diagram without the dot followed by bubbles
(the odd-bubble terms of (4.4)). -/
theorem arc_dot (μ : X) : ∀ (n : ℕ) {s : List (ℕ × Letter I)}, s.length + Chord.cr s < n →
    Valid s → Lettered flipL s → ∀ {a c : ℕ}, Same s a c → ∀ (Q : List (XLayer I))
    (t₀ : List (Letter I)),
    SignRel (LtL D Sc cs μ [] t₀ (ncr (canon s) + xcnt Q) ⊔
        BubTerm cs μ [] t₀ (chordLay [] (canon s) ++ Q))
      (xev cs μ [] t₀ (chordLay [] (canon s) ++ dotOn (s.map Prod.snd) c ++ Q))
      (xev cs μ [] t₀ (chordLay [] (canon s) ++ dotOn (s.map Prod.snd) a ++ Q)) := by
  intro n
  induction n with
  | zero => intro s h; omega
  | succ n ih =>
  intro s hn hv hl a c hac Q t₀
  by_cases hadj : ∃ r, Same s r (r + 1)
  · classical
    obtain ⟨r, hr, hmin⟩ : ∃ r, Same s r (r + 1) ∧ ∀ r' < r, ¬ Same s r' (r' + 1) :=
      ⟨Nat.find hadj, Nat.find_spec hadj, fun _ => Nat.find_min hadj⟩
    have hl2 : r + 2 ≤ s.length := hr.lt_right
    obtain ⟨x, hx⟩ : ∃ x, x = (s[r]'hr.lt_left).2 := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t, t = Chord.rmAt s r := ⟨_, rfl⟩
    have hvt : Valid t := ht ▸ hv.rmAt hr
    have hlt : Lettered flipL t := ht ▸ hl.rmAt hl2
    obtain ⟨hft, hct⟩ := canon_letters hvt hlt
    have hmeas : t.length + Chord.cr t < n := by
      rw [ht, Chord.length_rmAt s hl2]; have := Chord.cr_rmAt_le (s := s) hl2; omega
    have hv' : s.map Prod.snd = chStep (t.map Prod.snd) (.cup r x) := by
      rw [ht, hx]; exact map_snd_adj hl hr
    have hm : (Move.cup r x : Move (Letter I)).Ok (t.map Prod.snd).length := by
      simp [Chord.Move.Ok, ht, Chord.length_rmAt s hl2]; omega
    have hch : chordLay [] (canon s) =
        chordLay [] (canon t) ++ moveLay (t.map Prod.snd) (.cup r x) := by
      rw [Chord.canon_adj hv hr hmin, ← ht, ← hx, chordLay_append, hct]; simp [chordLay]
    have hncr : ncr (canon s) = ncr (canon t) := by
      rw [Chord.canon_adj hv hr hmin, ← ht, ncr_append]; simp [ncr]
    rw [hch, hncr, hv']
    have hPc := xChain_chordLay_canon hvt hlt
    by_cases hc : c = r ∨ c = r + 1
    · -- the dot is on the cup created last
      have key : SignRel (LtL D Sc cs μ [] t₀ (ncr (canon t) + xcnt Q) ⊔
            BubTerm cs μ [] t₀ (chordLay [] (canon t) ++ moveLay (t.map Prod.snd) (.cup r x) ++ Q))
          (xev cs μ [] t₀ (chordLay [] (canon t) ++ moveLay (t.map Prod.snd) (.cup r x) ++
            dotOn (chStep (t.map Prod.snd) (.cup r x)) (r + 1) ++ Q))
          (xev cs μ [] t₀ (chordLay [] (canon t) ++ moveLay (t.map Prod.snd) (.cup r x) ++
            dotOn (chStep (t.map Prod.snd) (.cup r x)) r ++ Q)) := by
        obtain ⟨u, w, huw, hu⟩ := exists_split_cup (l := t.map Prod.snd) (g := r) hm
        rw [huw, ← hu, moveLay_cup, chStep_cup,
          dotOn_eq' (u := u ++ [x]) (l := flipL x) (w := w) (by simp) (by simp), dotOn_eq]
        rw [huw] at hPc
        obtain ⟨p, r', hir, E⟩ := dotCup (cs := cs) (wt D μ w) x
        obtain ⟨q, hq⟩ := xev_oddBubble_ctx (t₀ := t₀) μ (chordLay [] (canon t)) Q u w E hir
          (hPc.cast rfl (by simp))
          ((xChain_xCupL x).app ((xChain_xDotL (flipL x)).whisk [x] []) (by simp) |>.cast rfl
            (by simp))
          ((xChain_xCupL x).app ((xChain_xDotL x).whisk [] [flipL x]) (by simp) |>.cast rfl
            (by simp))
          (xChain_xCupL x)
        refine ⟨p, ?_⟩
        have e1 : chordLay [] (canon t) ++ (xCupL x).map (xwhL u w) ++
            (xDotL (flipL x)).map (xwhL (u ++ [x]) w) ++ Q = chordLay [] (canon t) ++
              (xCupL x ++ (xDotL (flipL x)).map (xwhL [x] [])).map (xwhL u w) ++ Q := by
          simp
        have e2 : chordLay [] (canon t) ++ (xCupL x).map (xwhL u w) ++
            (xDotL x).map (xwhL u (flipL x :: w)) ++ Q = chordLay [] (canon t) ++
              (xCupL x ++ (xDotL x).map (xwhL [] [flipL x])).map (xwhL u w) ++ Q := by
          simp
        rw [e1, e2, hq, add_sub_cancel_left]
        exact Submodule.mem_sup_right (Submodule.smul_mem _ _
          (Submodule.subset_span ⟨_, IsBubbleProd.of_oddBubble μ x.2, rfl⟩))
      rcases hc with rfl | rfl
      · have ha : a = c + 1 := hv.unique hac.symm hr
        subst ha
        exact key.symm
      · have ha : a = r := hv.unique hac.symm hr.symm
        subst ha
        exact key
    · have ha : ¬ (a = r ∨ a = r + 1) := by
        rintro (rfl | rfl)
        · exact hc (Or.inr (hv.unique hac hr))
        · exact hc (Or.inl (hv.unique hac hr.symm))
      set c' := if c < r then c else c - 2 with hc'
      set a' := if a < r then a else a - 2 with ha'
      have ec : movePos (.cup r x) c' = c := by simp only [movePos, hc']; split_ifs <;> omega
      have ea : movePos (.cup r x) a' = a := by simp only [movePos, ha']; split_ifs <;> omega
      have hac' : Same t a' c' := by
        rw [ht, Chord.same_rmAt hl2]
        have e1 : Chord.rmIdx r a' = a := by simp only [Chord.rmIdx, ha']; split_ifs <;> omega
        have e2 : Chord.rmIdx r c' = c := by simp only [Chord.rmIdx, hc']; split_ifs <;> omega
        rw [e1, e2]; exact hac
      have hcl : c' < (t.map Prod.snd).length := by simpa using hac'.lt_right
      have hal : a' < (t.map Prod.snd).length := by simpa using hac'.lt_left
      have h1 := dot_move (cs := cs) (ν := μ) (t₀ := t₀) hm hcl (chordLay [] (canon t)) Q hPc
      have h2 := ih hmeas hvt hlt hac' (moveLay (t.map Prod.snd) (.cup r x) ++ Q) t₀
      have h3 := dot_move (cs := cs) (ν := μ) (t₀ := t₀) hm hal (chordLay [] (canon t)) Q hPc
      rw [ec] at h1
      rw [ea] at h3
      simp only [xcnt_append, xcnt_moveLay hm, xcnt_chordLay (l := []) hft] at h1 h2 h3
      simp only [ncr_cons_cup, ncr_nil, zero_add, add_zero] at h1 h2 h3 ⊢
      simp only [List.append_assoc] at h1 h2 h3 ⊢
      exact (h1.signRel.mono le_sup_left).symm.trans
        (h2.trans (h3.signRel.mono le_sup_left))
  · have hno : ∀ r, ¬ Same s r (r + 1) := fun r hr => hadj ⟨r, hr⟩
    have hne : s ≠ [] := by rintro rfl; have := hac.lt_left; simp at this
    obtain ⟨q, ho, hcl, hq, -⟩ := Chord.canon_cross hv hno hne
    have hilv := Chord.ilv_of_opn_cls hv (hno q) ho hcl
    have hql := hilv.lt
    set t := Chord.swapAt s q with ht
    have hvt : Valid t := hv.swapAt hql
    have hlt : Lettered flipL t := hl.swapAt hql (hno q)
    obtain ⟨hft, hct⟩ := canon_letters hvt hlt
    have hmeas : t.length + Chord.cr t < n := by
      rw [ht, Chord.length_swapAt]; have := Chord.cr_swapAt_lt hv hilv; omega
    have hv' : s.map Prod.snd = chStep (t.map Prod.snd) (.cross q) := by
      simp only [chStep, Chord.lstep, ht, ← Chord.map_swapAt, Chord.swapAt_swapAt]
    have hm : (Move.cross q : Move (Letter I)).Ok (t.map Prod.snd).length := by
      simpa [Chord.Move.Ok, ht] using hql
    have hch : chordLay [] (canon s) =
        chordLay [] (canon t) ++ moveLay (t.map Prod.snd) (.cross q) := by
      rw [hq, chordLay_append, hct]; simp [chordLay]
    have hncr : ncr (canon s) = ncr (canon t) + 1 := by
      rw [hq, ncr_append]; simp [ncr]
    rw [hch, hncr, hv']
    have hPc := xChain_chordLay_canon hvt hlt
    have hac' : Same t (Chord.tau q a) (Chord.tau q c) := by
      rw [ht, Chord.same_swapAt hql, Chord.tau_tau, Chord.tau_tau]; exact hac
    have hcl' : Chord.tau q c < (t.map Prod.snd).length := by simpa using hac'.lt_right
    have hal' : Chord.tau q a < (t.map Prod.snd).length := by simpa using hac'.lt_left
    have h1 := dot_move (cs := cs) (ν := μ) (t₀ := t₀) hm hcl' (chordLay [] (canon t)) Q hPc
    have h2 := ih hmeas hvt hlt hac' (moveLay (t.map Prod.snd) (.cross q) ++ Q) t₀
    have h3 := dot_move (cs := cs) (ν := μ) (t₀ := t₀) hm hal' (chordLay [] (canon t)) Q hPc
    simp only [movePos, Chord.tau_tau] at h1 h3
    simp only [xcnt_append, xcnt_moveLay hm, xcnt_chordLay (l := []) hft] at h1 h2 h3
    simp only [List.append_assoc] at h1 h2 h3 ⊢
    simp only [ncr_cons_cross, ncr_nil, zero_add] at h1 h2 h3
    rw [← add_assoc] at h2
    exact (h1.signRel.mono le_sup_left).symm.trans (h2.trans (h3.signRel.mono le_sup_left))

end Arcs

/-! ## Dots at the left ends of the arcs -/

section LeftEnds

open StringDiagrams.Chord (Same Valid Lettered)

/-- The left end of the arc through the position `i`. -/
noncomputable def lEnd (s : List (ℕ × Letter I)) (i : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, j < i ∧ Same s i j then Nat.find h else i

theorem lEnd_spec (s : List (ℕ × Letter I)) (i : ℕ) :
    (lEnd s i = i ∧ ¬ ∃ j, j < i ∧ Same s i j) ∨ (lEnd s i < i ∧ Same s i (lEnd s i)) := by
  classical
  unfold lEnd
  split_ifs with h
  · exact Or.inr ⟨(Nat.find_spec h).1, (Nat.find_spec h).2⟩
  · exact Or.inl ⟨rfl, h⟩

theorem lEnd_isLeft {s : List (ℕ × Letter I)} (hv : Valid s) (i : ℕ) :
    ¬ ∃ j, j < lEnd s i ∧ Same s (lEnd s i) j := by
  rcases lEnd_spec s i with ⟨e, h⟩ | ⟨hlt, h⟩
  · rwa [e]
  · rintro ⟨j, hj, hs⟩
    have := hv.unique h.symm hs
    omega

theorem lEnd_lt {s : List (ℕ × Letter I)} {i : ℕ} (hi : i < s.length) : lEnd s i < s.length := by
  rcases lEnd_spec s i with ⟨e, -⟩ | ⟨hlt, -⟩ <;> omega

variable (cs) in
/-- **The canonical spanning set**: the canonical chord diagrams of the pairings `s` of `v`, with
dots at the left ends of their arcs (any number on each arc), followed by products of bubbles in
the rightmost region. -/
def CanonSpan (μ : X) (v : List (Letter I)) :
    Submodule k ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ v)) :=
  Submodule.span k {f | ∃ (s : List (ℕ × Letter I)) (is : List ℕ)
    (β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])), Valid s ∧
      Lettered flipL s ∧ s.map Prod.snd = v ∧
      (∀ i ∈ is, i < s.length ∧ ¬ ∃ j, j < i ∧ Same s i j) ∧ IsBubbleProd cs μ β ∧
      f = xev cs μ [] v (chordLay [] (canon s) ++ dotsOn v is) ≫ bubAt D Sc μ v β}

theorem SignRel.comp_mem {ν : X} {s t t' : List (Letter I)}
    {T : Submodule k ((pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t'))}
    {S' : Submodule k ((pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t))}
    {f g : (pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)}
    {b : (pres D Sc).obj (ob D ν t) ⟶ (pres D Sc).obj (ob D ν t')}
    (h : SignRel S' f g) (hS : ∀ x ∈ S', x ≫ b ∈ T) (hg : g ≫ b ∈ T) : f ≫ b ∈ T := by
  obtain ⟨p, hp⟩ := h
  have e : f ≫ b = (f - zsign k p • g) ≫ b + zsign k p • (g ≫ b) := by
    rw [Preadditive.sub_comp, Linear.smul_comp, sub_add_cancel]
  rw [e]
  exact Submodule.add_mem _ (hS _ hp) (Submodule.smul_mem _ _ hg)

theorem bubTerm_comp_bubAt {ν : X} {s t : List (Letter I)} {L : List (XLayer I)}
    {T : Submodule k ((pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t))}
    {β : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν [])} (hβ : IsBubbleProd cs ν β)
    (hT : ∀ γ, IsBubbleProd cs ν γ → xev cs ν s t L ≫ bubAt D Sc ν t γ ∈ T) {x}
    (hx : x ∈ BubTerm cs ν s t L) : x ≫ bubAt D Sc ν t β ∈ T := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, rfl⟩ := hx
    rw [Category.assoc, ← bubAt_comp]
    exact hT _ (hγ.comp hβ)
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ a hx

/-- **Dots move to the left ends of their arcs**: a canonical diagram with dots, followed by a
product of bubbles, lies in the canonical span modulo diagrams with fewer crossings. The
odd-bubble terms have fewer dots and are handled by induction on the number of dots. -/
theorem canon_dots_mem (μ : X) {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered flipL s) :
    ∀ (N : ℕ) (is js : List ℕ), is.length + js.length ≤ N → (∀ i ∈ is, i < s.length) →
      (∀ j ∈ js, j < s.length ∧ ¬ ∃ i, i < j ∧ Same s j i) →
      ∀ {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])}, IsBubbleProd cs μ β →
      xev cs μ [] (s.map Prod.snd) (chordLay [] (canon s) ++ dotsOn (s.map Prod.snd) (is ++ js)) ≫
          bubAt D Sc μ (s.map Prod.snd) β ∈
        CanonSpan cs μ (s.map Prod.snd) ⊔ LtL D Sc cs μ [] (s.map Prod.snd) (ncr (canon s)) := by
  have hgen : ∀ (js : List ℕ), (∀ j ∈ js, j < s.length ∧ ¬ ∃ i, i < j ∧ Same s j i) →
      ∀ {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])}, IsBubbleProd cs μ β →
      xev cs μ [] (s.map Prod.snd) (chordLay [] (canon s) ++ dotsOn (s.map Prod.snd) ([] ++ js)) ≫
          bubAt D Sc μ (s.map Prod.snd) β ∈
        CanonSpan cs μ (s.map Prod.snd) ⊔ LtL D Sc cs μ [] (s.map Prod.snd) (ncr (canon s)) :=
    fun js hjs β hβ => Submodule.mem_sup_left (Submodule.subset_span
      ⟨s, js, β, hv, hl, rfl, hjs, hβ, by rw [List.nil_append]⟩)
  have hlow : ∀ {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])},
      IsBubbleProd cs μ β → ∀ x ∈ LtL D Sc cs μ [] (s.map Prod.snd) (ncr (canon s)),
      x ≫ bubAt D Sc μ (s.map Prod.snd) β ∈
        CanonSpan cs μ (s.map Prod.snd) ⊔ LtL D Sc cs μ [] (s.map Prod.snd) (ncr (canon s)) :=
    fun hβ x hx => Submodule.mem_sup_right (ltL_comp_bubAt hx hβ)
  have hP := xChain_chordLay_canon hv hl
  intro N
  induction N with
  | zero =>
    intro is js hlen _ hjs β hβ
    have : is = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact hgen js hjs hβ
  | succ N ihN =>
    intro is
    induction is with
    | nil => intro js _ _ hjs β hβ; exact hgen js hjs hβ
    | cons i is ihis =>
      intro js hlen his hjs β hβ
      have hi : i < s.length := his i List.mem_cons_self
      have his' : ∀ j ∈ is, j < s.length := fun j hj => his j (List.mem_cons_of_mem _ hj)
      have hall : ∀ j ∈ is ++ js, j < (s.map Prod.snd).length := by
        intro j hj
        rcases List.mem_append.1 hj with hj | hj
        · simpa using his' j hj
        · simpa using (hjs j hj).1
      -- the first dot moves to the left end of its arc
      have step1 : SignRel (LtL D Sc cs μ [] (s.map Prod.snd) (ncr (canon s)) ⊔
            BubTerm cs μ [] (s.map Prod.snd)
              (chordLay [] (canon s) ++ dotsOn (s.map Prod.snd) (is ++ js)))
          (xev cs μ [] (s.map Prod.snd) (chordLay [] (canon s) ++ dotOn (s.map Prod.snd) i ++
            dotsOn (s.map Prod.snd) (is ++ js)))
          (xev cs μ [] (s.map Prod.snd) (chordLay [] (canon s) ++
            dotOn (s.map Prod.snd) (lEnd s i) ++ dotsOn (s.map Prod.snd) (is ++ js))) := by
        rcases lEnd_spec s i with ⟨e, -⟩ | ⟨-, hs⟩
        · rw [e]; exact SignRel.refl _
        · have := arc_dot (cs := cs) μ _ (Nat.lt_succ_self _) hv hl hs.symm
            (dotsOn (s.map Prod.snd) (is ++ js)) (s.map Prod.snd)
          simpa using this
      -- the dot at the left end joins the dots already there
      have hL : lEnd s i < (s.map Prod.snd).length := by simpa using lEnd_lt hi
      have hperm := dotsOn_perm (cs := cs) (ν := μ) (t₀ := s.map Prod.snd)
        (n := ncr (canon s)) (t := s.map Prod.snd)
        (List.perm_middle (a := lEnd s i) (l₁ := is) (l₂ := js)).symm
        (by
          intro j hj
          rcases List.mem_cons.1 hj with rfl | hj
          · exact hL
          · exact hall j hj)
        (chordLay [] (canon s)) [] hP
      simp only [List.append_nil, dotsOn_cons] at hperm
      have h2 : xev cs μ [] (s.map Prod.snd) (chordLay [] (canon s) ++
            dotOn (s.map Prod.snd) (lEnd s i) ++ dotsOn (s.map Prod.snd) (is ++ js)) ≫
          bubAt D Sc μ (s.map Prod.snd) β ∈
            CanonSpan cs μ (s.map Prod.snd) ⊔ LtL D Sc cs μ [] (s.map Prod.snd) (ncr (canon s)) := by
        rw [← List.append_assoc] at hperm
        refine hperm.signRel.comp_mem (hlow hβ) ?_
        refine ihis (lEnd s i :: js) (by simp at hlen ⊢; omega) his' ?_ hβ
        intro j hj
        rcases List.mem_cons.1 hj with rfl | hj
        · exact ⟨lEnd_lt hi, lEnd_isLeft hv i⟩
        · exact hjs j hj
      simp only [List.cons_append, dotsOn_cons, ← List.append_assoc]
      refine step1.comp_mem ?_ h2
      intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
      rw [Preadditive.add_comp]
      refine Submodule.add_mem _ (hlow hβ y hy) (bubTerm_comp_bubAt hβ ?_ hz)
      intro γ hγ
      have := ihN (is ++ js) [] (by simp at hlen ⊢; omega) (fun j hj => by simpa using hall j hj)
        (by simp) hγ
      simpa using this

end LeftEnds

/-! ## Spanning -/

section Span

open StringDiagrams.Chord (Same Valid Lettered)

theorem thruShort_nil (μ : X) (v : List (Letter I)) : thruShort D Sc μ [] v = ⊥ := by
  rw [thruShort, Submodule.span_eq_bot]
  rintro _ ⟨u, g, h, hu, rfl⟩
  simp at hu

/-- **A move diagram followed by bubbles lies in the canonical span modulo lower terms**, given
`R3Rel` and `CupCurlRel`. -/
theorem mvSp_gen_mem (hR : R3Rel D Sc cs) (hU : CupCurlRel D Sc cs) (μ : X)
    {v : List (Letter I)} {ms : List (Mv I)} (hch : MvChain [] ms v)
    {β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])} (hβ : IsBubbleProd cs μ β) :
    xev cs μ [] v (mvLay ms) ≫ bubAt D Sc μ v β ∈
      CanonSpan cs μ v ⊔ LtL D Sc cs μ [] v (xcnt (mvLay ms)) := by
  obtain ⟨E, is, hE, hlet, hn, his, hdiff⟩ := mv_to_chord (cs := cs) μ ms hch
  have hlow : ∀ x ∈ LtL D Sc cs μ [] v (xcnt (mvLay ms)),
      x ≫ bubAt D Sc μ v β ∈ CanonSpan cs μ v ⊔ LtL D Sc cs μ [] v (xcnt (mvLay ms)) :=
    fun x hx => Submodule.mem_sup_right (ltL_comp_bubAt hx hβ)
  refine hdiff.signRel.comp_mem hlow ?_
  have hsD : XChain [] (chordLay [] E) v := by
    have := xChain_chordLay (l := []) hE; rwa [hlet] at this
  rcases chordLay_normal_form hR hU hE μ v with h | ⟨hfc, hnc, hdc⟩
  · refine hlow _ ?_
    rw [xev_append cs _ hsD]
    have := ltL_comp_xev (r := v) h (dotsOn v is)
    rwa [xcnt_dotsOn, add_zero, hn] at this
  · obtain ⟨s, hs⟩ : ∃ s, s = run flipL E := ⟨_, rfl⟩
    rw [← hs] at hfc hnc hdc
    have hvs : Valid s := hs ▸ (Chord.inv_run hE).1
    have hls : Lettered flipL s := hs ▸ Chord.lettered_run flipL_involutive hE
    have hsv : s.map Prod.snd = v := by rw [hs, Chord.snd_run, ← hlet]
    have hsc : XChain [] (chordLay [] (canon s)) v := by
      have := xChain_chordLay_canon hvs hls; rwa [hsv] at this
    have h2 := hdc.append_right (t := v) hsD hsc (dotsOn v is)
    rw [xcnt_dotsOn, add_zero, hn] at h2
    refine h2.signRel.comp_mem hlow ?_
    subst hsv
    have := canon_dots_mem (cs := cs) μ hvs hls is.length is [] (by simp)
      (fun i hi => by simpa using his i hi) (by simp) hβ
    rwa [List.append_nil, hnc, hn] at this

/-- **The canonical diagrams span `Hom(1_μ, E_v 1_μ)`, given Reidemeister 3 and the two curl
relations** ([BE2] Theorem 8.1, spanning part, for an empty bottom boundary and the canonical
choice of reduced matchings and of distinguished points): every 2-morphism `1_μ → E_v 1_μ` is a
linear combination of the canonical chord diagrams of the pairings of `v`, with dots at the left
ends of their arcs, followed by products of bubbles in the rightmost region.

The hypotheses `R3Rel` (Reidemeister 3 in all orientations up to sign modulo lower terms),
`CapCurlRel` and `CupCurlRel` (a crossing followed by a cap, a cup followed by a crossing: lower
terms) are not proved here. -/
theorem mem_canonSpan_of_localRels (hR : R3Rel D Sc cs) (hC : CapCurlRel D Sc cs)
    (hU : CupCurlRel D Sc cs) (μ : X) (v : List (Letter I))
    (f : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ v)) :
    f ∈ CanonSpan cs μ v := by
  have key : ∀ c (L : List (XLayer I)), xcnt L ≤ c → xev cs μ [] v L ∈ CanonSpan cs μ v := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ihc =>
    intro L hL
    have hlo : ∀ n ≤ c, LtL D Sc cs μ [] v n ≤ CanonSpan cs μ v := by
      intro n hn
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨L', hL', rfl⟩
      exact ihc (xcnt L') (by omega) L' le_rfl
    have hcap := capElim' μ [] hR hC hU c v L hL
    rw [CapTarget, thruShort_nil, sup_bot_eq, MvSp] at hcap
    generalize xev cs μ [] v L = x at hcap
    induction hcap using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ms, β, hch, hcc, hβ, rfl⟩ := hx
      exact (sup_le le_rfl (hlo _ hcc)) (mvSp_gen_mem hR hU μ hch hβ)
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  have hf := mem_span_cl (D := D) (Sc := Sc) μ f
  refine (Submodule.span_le.mpr ?_) hf
  rintro _ ⟨L, -, rfl⟩
  rw [← xev_map_ofL cs]
  exact key _ _ le_rfl

end Span

/-! ## The form of Theorem 8.1 -/

section Form

open StringDiagrams.Chord (Same Valid Lettered)

/-- The canonical one-sided diagrams for the word `v`: the canonical chord diagram of a pairing of
`v` (canonical reduced matching), followed by dots at the left ends of its arcs (the distinguished
points of the strands). -/
def canonDiagrams (v : List (Letter I)) : Set (List (XLayer I)) :=
  {C | ∃ (s : List (ℕ × Letter I)) (is : List ℕ), Valid s ∧ Lettered flipL s ∧
    s.map Prod.snd = v ∧ (∀ i ∈ is, i < s.length ∧ ¬ ∃ j, j < i ∧ Same s i j) ∧
    C = chordLay [] (canon s) ++ dotsOn v is}

theorem canonSpan_le_diagBubSpan (μ : X) (v : List (Letter I)) :
    CanonSpan cs μ v ≤ diagBubSpan D Sc cs μ [] v (canonDiagrams v) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨s, is, β, hv, hl, hsv, his, hβ, rfl⟩
  exact Submodule.subset_span ⟨_, ⟨s, is, hv, hl, hsv, his, rfl⟩, β, hβ.isBub, rfl⟩

/-- **[BE2] Theorem 8.1, spanning part, for an empty bottom boundary, given Reidemeister 3 and the
two curl relations**: the canonical diagrams `canonDiagrams v` (canonical reduced matching of each
pairing of `v`, dots at the left ends of the arcs) followed by the image of `β_μ` in the rightmost
region span `Hom(1_μ, E_v 1_μ)`. In this form it composes with `diagBubSpan_bendL_eq_top`.
The hypotheses `R3Rel`, `CapCurlRel` and `CupCurlRel` are not proved here. -/
theorem diagBubSpan_canonDiagrams_eq_top (hR : R3Rel D Sc cs) (hC : CapCurlRel D Sc cs)
    (hU : CupCurlRel D Sc cs) (μ : X) (v : List (Letter I)) :
    diagBubSpan D Sc cs μ [] v (canonDiagrams v) = ⊤ :=
  eq_top_iff.2 fun f _ => canonSpan_le_diagBubSpan μ v (mem_canonSpan_of_localRels hR hC hU μ v f)

end Form

end OddMath.SKM
