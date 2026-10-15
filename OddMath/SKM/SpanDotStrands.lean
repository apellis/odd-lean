/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanTwoSided
import OddMath.SKM.SpanMatchings

/-!
# Dots move along the strands of a matching

Towards J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 8.1
for a general bottom boundary (the decorated matchings of [BE2] §8). The paper omits the proof,
referring to M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1,
Proposition 3.11: a dot moves along its strand, through crossings modulo lower terms, and around
cups and caps up to sign (and, for odd colours, terms with the odd bubble, [BE2] (4.3), (4.4)).

We work with a one-sided diagram `B₀ : 1 → E_{l₀}` (the *base*, in the application the nested
cups bending the bottom boundary up) whose pairing is the state `T₀`, followed by a *decorated*
matching `ds : List (DTMove I)`: moves of two-sided matchings (cups, crossings, caps, `TMove`) and
dots, at absolute positions (`dLay`). The strands are tracked by the states `tRun flipL 0 T₀`.

## Main results

* `DotBase.arc_dot`: a dot at the top of the decorated diagram slides to the other end of its arc,
  up to sign modulo lower terms and terms with the odd bubble and one dot fewer (given the same for
  the base).
* `DotBase.dot_up`: a dot anywhere in the diagram moves up its strand to the top; the strand id
  it reaches is the id of its starting point renamed along the joins of the later caps (`tRen`).
* `DotBase.dots_up`: all dots of a decorated matching move to the top, modulo lower terms and
  decorated diagrams with fewer dots (`DecSpan`).
* `dotBase_tStart`: the nested cups `cupA a*` bending the bottom boundary up form a base.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation
open StringDiagrams.Chord (Move Fits run Iso rl rlId TMove TState tStep tRun TFits TInv ncr₂ jn idD
  Same Valid)

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} {cs : CScalars Sc}

/-! ## Moves of matchings at absolute positions -/

section Global

/-- A move of a two-sided matching shifted `n` positions to the right. -/
def shiftT (n : ℕ) : TMove (Letter I) → TMove (Letter I)
  | .mv m => .mv (shiftM n m)
  | .cap g => .cap (n + g)

theorem tStep_shift (n : ℕ) (T : TState (Letter I)) (m : TMove (Letter I)) :
    tStep flipL n T m = tStep flipL 0 T (shiftT n m) := by
  rcases m with (⟨g, a⟩ | p) | g <;> simp [Chord.tStep, shiftT, shiftM, add_assoc]

theorem ok_shift (n : ℕ) (s : List (ℕ × Letter I)) (m : TMove (Letter I)) :
    m.Ok flipL n s ↔ (shiftT n m).Ok flipL 0 s := by
  rcases m with (⟨g, a⟩ | p) | g <;> simp [TMove.Ok, shiftT, shiftM, add_assoc]

theorem tRun_shift (n : ℕ) : ∀ (T : TState (Letter I)) (R : List (TMove (Letter I))),
    tRun flipL n T R = tRun flipL 0 T (R.map (shiftT n))
  | _, [] => rfl
  | T, m :: R => by
    show R.foldl (tStep flipL n) (tStep flipL n T m) =
      (R.map (shiftT n)).foldl (tStep flipL 0) (tStep flipL 0 T (shiftT n m))
    rw [tStep_shift]; exact tRun_shift n _ R

theorem tFits_shift (n : ℕ) : ∀ (T : TState (Letter I)) (R : List (TMove (Letter I))),
    TFits flipL n T R ↔ TFits flipL 0 T (R.map (shiftT n))
  | _, [] => Iff.rfl
  | T, m :: R => by
    simp only [Chord.TFits, List.map_cons]
    rw [ok_shift, tStep_shift, tFits_shift n _ R]

theorem ncr₂_shift (n : ℕ) : ∀ R : List (TMove (Letter I)), ncr₂ (R.map (shiftT n)) = ncr₂ R
  | [] => rfl
  | m :: R => by
    rw [List.map_cons, ncr₂_cons, ncr₂_cons _ R, ncr₂_shift n R]
    rcases m with (⟨g, a⟩ | p) | g <;> rfl

theorem tmLay_shift (u : List (Letter I)) {l : List (Letter I)} {m : TMove (Letter I)}
    (hm : ∀ mm, m = .mv mm → mm.Ok l.length) :
    (tmLay l m).map (xwhL u []) = tmLay (u ++ l) (shiftT u.length m) ∧
      u ++ tLet l m = tLet (u ++ l) (shiftT u.length m) := by
  rcases m with mm | g
  · obtain ⟨h1, h2⟩ := moveLay_shift u [] (hm mm rfl)
    simp only [List.append_nil] at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  · have e1 : (u ++ l).drop (u.length + g) = l.drop g := by
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega)]; simp
    have e2 : (u ++ l).take (u.length + g) = u ++ l.take g := by
      rw [List.take_append]; simp
    refine ⟨?_, ?_⟩
    · simp only [tmLay, shiftT, e1, e2]
      split <;> simp
    · have e3 : (u ++ l).drop (u.length + g + 2) = l.drop (g + 2) := by
        rw [show u.length + g + 2 = u.length + (g + 2) by omega]; simp
      simp only [tLet, shiftT, e2, e3, List.append_assoc]

/-- The position reached from `x` through a move (for a cap, `x` is not one of its legs). -/
def tPos : TMove (Letter I) → ℕ → ℕ
  | .mv m, x => movePos m x
  | .cap g, x => if x < g then x else x - 2

/-- `x` is a leg of the cap `m`. -/
def CapLeg : TMove (Letter I) → ℕ → Prop
  | .mv _, _ => False
  | .cap g, x => x = g ∨ x = g + 1

/-- The renaming of strand ids by a move: a cap renames the id of its right leg to the id of its
left leg. -/
def stepRen (n : ℕ) (T : TState (Letter I)) : TMove (Letter I) → ℕ → ℕ
  | .mv _ => id
  | .cap g => rlId (idD T.st (n + g + 1)) (idD T.st (n + g))

/-- **The renaming of strand ids along a matching**: the id at the top of the strand with id `x`
at the bottom. -/
def tRen (n : ℕ) : TState (Letter I) → List (TMove (Letter I)) → ℕ → ℕ
  | _, [] => id
  | T, m :: R => fun x => tRen n (tStep flipL n T m) R (stepRen n T m x)

theorem tRen_shift (n : ℕ) : ∀ (T : TState (Letter I)) (R : List (TMove (Letter I))) (x : ℕ),
    tRen n T R x = tRen 0 T (R.map (shiftT n)) x
  | _, [], _ => rfl
  | T, m :: R, x => by
    simp only [tRen, List.map_cons]
    rw [tStep_shift, tRen_shift n _ R]
    congr 1
    rcases m with (⟨g, a⟩ | p) | g <;> simp [stepRen, shiftT, add_assoc]

theorem tFits_append : ∀ (T : TState (Letter I)) (R R' : List (TMove (Letter I))),
    TFits flipL 0 T (R ++ R') ↔ TFits flipL 0 T R ∧ TFits flipL 0 (tRun flipL 0 T R) R'
  | _, [], _ => by simp [Chord.TFits, Chord.tRun]
  | T, m :: R, R' => by
    simp only [List.cons_append, Chord.TFits, tFits_append _ R R', and_assoc]
    rfl

theorem tRun_append (T : TState (Letter I)) (R R' : List (TMove (Letter I))) :
    tRun flipL 0 T (R ++ R') = tRun flipL 0 (tRun flipL 0 T R) R' := by
  simp [Chord.tRun, List.foldl_append]

theorem tRun_snoc (T : TState (Letter I)) (R : List (TMove (Letter I))) (m : TMove (Letter I)) :
    tRun flipL 0 T (R ++ [m]) = tStep flipL 0 (tRun flipL 0 T R) m := by
  simp [Chord.tRun, List.foldl_append]

/-- The letters of a move apply: for a cap, the two legs carry dual letters. -/
def LOk (l : List (Letter I)) : TMove (Letter I) → Prop
  | .mv m => m.Ok l.length
  | .cap g => ∃ v y w, l = v ++ flipL y :: y :: w ∧ v.length = g

theorem lOk_of_ok {T : TState (Letter I)} {l : List (Letter I)} (hl : T.st.map Prod.snd = l)
    {m : TMove (Letter I)} (hm : m.Ok flipL 0 T.st) : LOk l m := by
  have hlen : T.st.length = l.length := by rw [← hl, List.length_map]
  rcases m with (⟨g, a⟩ | p) | g
  · simp only [TMove.Ok] at hm; show g ≤ l.length; omega
  · simp only [TMove.Ok] at hm; show p + 1 < l.length; omega
  · obtain ⟨A, B, hA, hB, hAB, -⟩ := hm
    have hr : g + 1 < T.st.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hB; cases hB
    obtain ⟨v, x, y, w, hl', hv⟩ := exists_split_cross (l := l) (p := g) (by omega)
    have hx : l[g]? = some A.2 := by
      rw [← hl, List.getElem?_map]; simp only [zero_add] at hA; rw [hA]; rfl
    have hy : l[g + 1]? = some B.2 := by
      rw [← hl, List.getElem?_map]; simp only [zero_add] at hB; rw [hB]; rfl
    rw [hl', ← hv] at hx hy
    simp at hx hy
    refine ⟨v, y, w, ?_, hv⟩
    rw [hl', hx, hy, hAB]

/-- **A move of a matching on the letters**: the letters after the move, the layers of the move,
and its crossings. -/
theorem tStep_spec {T : TState (Letter I)} {l : List (Letter I)} (hl : T.st.map Prod.snd = l)
    {m : TMove (Letter I)} (hm : m.Ok flipL 0 T.st) :
    (tStep flipL 0 T m).st.map Prod.snd = tLet l m ∧ XChain l (tmLay l m) (tLet l m) ∧
      xcnt (tmLay l m) = ncr₂ [m] := by
  have hL := lOk_of_ok hl hm
  rcases m with (⟨g, a⟩ | p) | g
  · have hL' : (Move.cup g a).Ok l.length := hL
    refine ⟨?_, xChain_moveLay hL', by rw [tmLay, xcnt_moveLay hL']; simp [ncr, ncr₂]⟩
    simp only [Chord.tStep, zero_add, Chord.map_insAt, hl]; rfl
  · have hL' : (Move.cross (α := Letter I) p).Ok l.length := hL
    refine ⟨?_, xChain_moveLay hL', by rw [tmLay, xcnt_moveLay hL']; simp [ncr, ncr₂]⟩
    simp only [Chord.tStep, zero_add, Chord.map_swapAt, hl]; rfl
  · obtain ⟨v, y, w, rfl, rfl⟩ := hL
    have hr : v.length + 1 < T.st.length := by
      have := congrArg List.length hl; simp at this; omega
    obtain ⟨hcap, hlet⟩ := tmLay_cap v w (flipL y) y
    refine ⟨?_, ?_, by rw [hcap]; simp [ncr₂]⟩
    · simp only [Chord.tStep, zero_add]
      rw [Chord.map_snd_jn _ _ hr, Chord.map_rmAt, hl, hlet]
      simp [Chord.rmAt]
    · rw [hcap, hlet]; simpa using (xChain_xCapL y).whisk v w

theorem idD_of_idAt {s : List (ℕ × Letter I)} {i c : ℕ} (h : Chord.idAt s i = some c) :
    idD s i = c := by
  rw [idD, h]; rfl

/-- **Following a strand through a move**: the position is `tPos`, the id is renamed by
`stepRen`. -/
theorem idD_tStep {T : TState (Letter I)} {m : TMove (Letter I)} (hm : m.Ok flipL 0 T.st) {x : ℕ}
    (hx : x < T.st.length) (hxm : ¬ CapLeg m x) :
    tPos m x < (tStep flipL 0 T m).st.length ∧
      idD (tStep flipL 0 T m).st (tPos m x) = stepRen 0 T m (idD T.st x) := by
  rcases m with (⟨g, a⟩ | p) | g
  · simp only [TMove.Ok] at hm
    simp only [Chord.tStep, tPos, movePos, stepRen, zero_add, id]
    refine ⟨?_, ?_⟩
    · rw [Chord.length_insAt _ (by omega)]; split_ifs <;> omega
    · rw [idD, idD, Chord.idAt_insAt (by omega)]
      split_ifs <;> first | rfl | omega
  · simp only [TMove.Ok] at hm
    simp only [Chord.tStep, tPos, movePos, stepRen, zero_add, id]
    refine ⟨?_, ?_⟩
    · rw [Chord.length_swapAt]; unfold Chord.tau; split_ifs <;> omega
    · rw [idD, idD, Chord.idAt_swapAt (by omega), Chord.tau_tau]
  · obtain ⟨A, B, hA, hB, -, -⟩ := hm
    simp only [zero_add] at hA hB
    have hr : g + 1 < T.st.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hB; cases hB
    have hxa : Chord.idAt T.st g = some A.1 := by simp [Chord.idAt, hA]
    have hxb : Chord.idAt T.st (g + 1) = some B.1 := by simp [Chord.idAt, hB]
    simp only [CapLeg, not_or] at hxm
    simp only [Chord.tStep, tPos, stepRen, zero_add]
    have hu := Chord.idAt_jn_unrm hr hxa hxb (u := x) hxm
    refine ⟨?_, ?_⟩
    · rw [Chord.length_jn hr]; split_ifs <;> omega
    · have e : (if x < g then x else x - 2) = Chord.unrm g x := rfl
      rw [e, idD, hu, Chord.idAt_eq_some hx, idD_of_idAt hxa, idD_of_idAt hxb]
      simp [idD, Chord.idAt_eq_some hx]

end Global

/-! ## Decorated matchings -/

section DecoratedMatchings

/-- A move of a decorated matching: a move of a two-sided matching (a cup, a crossing or a cap),
or a dot on the strand at a position. -/
inductive DTMove (I : Type u)
  /-- A cup, a crossing or a cap. -/
  | tm (m : TMove (Letter I))
  /-- A dot on the strand at position `i`. -/
  | dt (i : ℕ)

namespace DTMove

/-- The underlying matching. -/
def tmoves : List (DTMove I) → List (TMove (Letter I))
  | [] => []
  | tm m :: ds => m :: tmoves ds
  | dt _ :: ds => tmoves ds

/-- The number of dots. -/
def ndots : List (DTMove I) → ℕ
  | [] => 0
  | tm _ :: ds => ndots ds
  | dt _ :: ds => ndots ds + 1

/-- The dots, as pairs (height, position); the height is the number of moves below the dot. -/
def dotPts : List (DTMove I) → List (ℕ × ℕ)
  | [] => []
  | tm _ :: ds => (dotPts ds).map fun q => (q.1 + 1, q.2)
  | dt i :: ds => (0, i) :: dotPts ds

@[simp] theorem tmoves_append : ∀ ds es : List (DTMove I),
    tmoves (ds ++ es) = tmoves ds ++ tmoves es
  | [], _ => rfl
  | tm m :: ds, es => by simp [tmoves, tmoves_append ds es]
  | dt _ :: ds, es => by simp [tmoves, tmoves_append ds es]

@[simp] theorem ndots_append : ∀ ds es : List (DTMove I),
    ndots (ds ++ es) = ndots ds + ndots es
  | [], _ => by simp [ndots]
  | tm m :: ds, es => by simp [ndots, ndots_append ds es]
  | dt _ :: ds, es => by simp [ndots, ndots_append ds es]; omega

@[simp] theorem tmoves_map_tm (R : List (TMove (Letter I))) : tmoves (R.map tm) = R := by
  induction R with
  | nil => rfl
  | cons m R ih => simp [tmoves, ih]

@[simp] theorem ndots_map_tm (R : List (TMove (Letter I))) : ndots (R.map tm) = 0 := by
  induction R with
  | nil => rfl
  | cons m R ih => simp [ndots, ih]

@[simp] theorem tmoves_dt (i : ℕ) : tmoves [(dt i : DTMove I)] = [] := rfl

@[simp] theorem tmoves_tm (m : TMove (Letter I)) : tmoves [(tm m : DTMove I)] = [m] := rfl

theorem length_dotPts : ∀ ds : List (DTMove I), (dotPts ds).length = ndots ds
  | [] => rfl
  | tm _ :: ds => by simp [dotPts, ndots, length_dotPts ds]
  | dt _ :: ds => by simp [dotPts, ndots, length_dotPts ds]

end DTMove

open DTMove

/-- **The layers of a decorated matching** (read from the bottom) starting from the letters
`l`. -/
def dLay : List (Letter I) → List (DTMove I) → List (XLayer I)
  | _, [] => []
  | l, .tm m :: ds => tmLay l m ++ dLay (tLet l m) ds
  | l, .dt i :: ds => dotOn l i ++ dLay l ds

/-- The dots of a decorated matching are on strands present. -/
def DOk₂ : List (Letter I) → List (DTMove I) → Prop
  | _, [] => True
  | l, .tm m :: ds => DOk₂ (tLet l m) ds
  | l, .dt i :: ds => i < l.length ∧ DOk₂ l ds

theorem dLay_append : ∀ (l : List (Letter I)) (ds es : List (DTMove I)),
    dLay l (ds ++ es) = dLay l ds ++ dLay ((tmoves ds).foldl tLet l) es
  | _, [], _ => rfl
  | l, .tm m :: ds, es => by
    simp only [List.cons_append, dLay, tmoves, List.foldl_cons, dLay_append _ ds es,
      List.append_assoc]
  | l, .dt i :: ds, es => by
    simp only [List.cons_append, dLay, tmoves, dLay_append _ ds es, List.append_assoc]

theorem dOk₂_append : ∀ (l : List (Letter I)) (ds es : List (DTMove I)),
    DOk₂ l (ds ++ es) ↔ DOk₂ l ds ∧ DOk₂ ((tmoves ds).foldl tLet l) es
  | _, [], _ => by simp [DOk₂, tmoves]
  | l, .tm m :: ds, es => by
    simp only [List.cons_append, DOk₂, tmoves, List.foldl_cons, dOk₂_append _ ds es]
  | l, .dt i :: ds, es => by
    simp only [List.cons_append, DOk₂, tmoves, dOk₂_append _ ds es, and_assoc]

theorem dLay_map_tm : ∀ (l : List (Letter I)) (R : List (TMove (Letter I))),
    dLay l (R.map .tm) = tLay l R
  | _, [] => rfl
  | l, m :: R => by simp only [List.map_cons, dLay, tLay, dLay_map_tm _ R]

theorem dOk₂_map_tm : ∀ (l : List (Letter I)) (R : List (TMove (Letter I))),
    DOk₂ l (R.map .tm)
  | _, [] => trivial
  | l, m :: R => dOk₂_map_tm (tLet l m) R

theorem dotOn_of_le {t : List (Letter I)} {i : ℕ} (h : t.length ≤ i) : dotOn t i = [] := by
  unfold dotOn; rw [List.drop_eq_nil_of_le h]

theorem xChain_dotOn' (t : List (Letter I)) (i : ℕ) : XChain t (dotOn t i) t := by
  by_cases h : i < t.length
  · exact xChain_dotOn h
  · rw [dotOn_of_le (by omega)]; rfl

/-- **The layers of a decorated matching on the letters.** -/
theorem dLay_spec : ∀ (ds : List (DTMove I)) {T : TState (Letter I)} {l : List (Letter I)},
    T.st.map Prod.snd = l → TFits flipL 0 T (tmoves ds) →
    (tRun flipL 0 T (tmoves ds)).st.map Prod.snd = (tmoves ds).foldl tLet l ∧
      XChain l (dLay l ds) ((tmoves ds).foldl tLet l) ∧ xcnt (dLay l ds) = ncr₂ (tmoves ds)
  | [], _, _, hl, _ => ⟨hl, rfl, rfl⟩
  | .tm m :: ds, T, l, hl, hf => by
    obtain ⟨h1, h2, h3⟩ := tStep_spec hl hf.1
    obtain ⟨h4, h5, h6⟩ := dLay_spec ds h1 hf.2
    exact ⟨h4, h2.append h5, by rw [dLay, xcnt_append, h3, h6, tmoves]; exact (ncr₂_cons m _).symm⟩
  | .dt i :: ds, T, l, hl, hf => by
    obtain ⟨h4, h5, h6⟩ := dLay_spec ds hl hf
    exact ⟨h4, (xChain_dotOn' l i).append h5, by rw [dLay, xcnt_append, xcnt_dotOn, h6, zero_add]; rfl⟩

end DecoratedMatchings

/-! ## A dot passes a move of a matching -/

section DotPass

theorem ncr₂_mv (m : Move (Letter I)) : ncr₂ [TMove.mv m] = ncr [m] := by
  cases m <;> rfl

/-- **A dot passes a move of a matching** (not a cap it ends on), up to sign modulo lower
terms. -/
theorem dot_tm_pass {W : List (Letter I)} {m : TMove (Letter I)} (hm : LOk W m) {x : ℕ}
    (hx : x < W.length) (hxm : ¬ CapLeg m x) {ν : X} {s₀ t₀ : List (Letter I)}
    (Pre Q : List (XLayer I)) (hP : XChain s₀ Pre W) :
    XLt cs ν s₀ t₀ (xcnt Pre + ncr₂ [m] + xcnt Q) (Pre ++ dotOn W x ++ tmLay W m ++ Q)
      (Pre ++ tmLay W m ++ dotOn (tLet W m) (tPos m x) ++ Q) := by
  rcases m with mm | g
  · rw [ncr₂_mv]
    exact dot_move hm hx Pre Q hP
  · obtain ⟨v, y, w, rfl, rfl⟩ := hm
    obtain ⟨hcap, hlet⟩ := tmLay_cap v w (flipL y) y
    rw [hcap, hlet]
    simp only [CapLeg, not_or] at hxm
    simp only [tPos]
    have h0 : ncr₂ [TMove.cap (α := Letter I) v.length] = 0 := rfl
    rw [h0]
    split_ifs with hxv
    · obtain ⟨v1, l, M, rfl, rfl⟩ := exists_split_dot (t := v) hxv
      rw [dotOn_eq' (u := v1) (l := l) (w := M ++ flipL y :: y :: w) (by simp) rfl,
        dotOn_eq' (u := v1) (l := l) (w := M ++ w) (by simp) rfl]
      have hB : XChain (M ++ [flipL y, y]) ((xCapL y).map (xwhL M [])) M := by
        simpa using (xChain_xCapL y).whisk M []
      exact XLt.ichg Pre Q v1 w (xChain_xDotL l) hB (hP.cast rfl (by simp)) (by simp) (by simp)
    · obtain ⟨M, l, w1, rfl, hM⟩ := exists_split_dot (t := w) (i := x - v.length - 2)
        (by simp at hx; omega)
      rw [dotOn_eq' (u := v ++ flipL y :: y :: M) (l := l) (w := w1) (by simp) (by simp; omega),
        dotOn_eq' (u := v ++ M) (l := l) (w := w1) (by simp) (by simp; omega)]
      have hB : XChain (M ++ [l]) ((xDotL l).map (xwhL M [])) (M ++ [l]) := by
        simpa using (xChain_xDotL l).whisk M []
      exact (XLt.ichg Pre Q v w1 (xChain_xCapL y) hB (hP.cast rfl (by simp)) (by simp)
        (by simp)).symm

/-- **A local relation with an odd bubble above it, in context**: the odd bubble moves to the
rightmost region at the top. -/
theorem xev_oddBubble_ctx_above {i : I} (μ : X) {s₀ t₀ : List (Letter I)}
    (pre post : List (XLayer I)) (u v : List (Letter I)) {s : List (Letter I)}
    {A B C : List (XLayer I)} {p : ZMod 2} {r : k}
    (E : xev cs (wt D μ v) s [] A = zsign k p • xev cs (wt D μ v) s [] B +
      r • (xev cs (wt D μ v) s [] C ≫ oddBubble cs i (wt D μ v)))
    (hir : D.parity i = 1 ∨ r = 0)
    (hpre : XChain s₀ pre (u ++ s ++ v)) (hA : XChain s A []) (hB : XChain s B [])
    (hC : XChain s C []) :
    ∃ q : ZMod 2, xev cs μ s₀ t₀ (pre ++ A.map (xwhL u v) ++ post) =
      zsign k p • xev cs μ s₀ t₀ (pre ++ B.map (xwhL u v) ++ post) +
        (zsign k q * r) • (xev cs μ s₀ t₀ (pre ++ C.map (xwhL u v) ++ post) ≫
          bubAt D Sc μ t₀ (oddBubble cs i μ)) := by
  rcases hir with hi | rfl
  · obtain ⟨q, hq⟩ := bubAt_comp_xev cs (μ := μ) (s := u ++ [] ++ v) (t := t₀) post
      (IsBubbleProd.of_oddBubble μ i)
    refine ⟨q, ?_⟩
    rw [xev_ctx cs μ pre post u v hpre hA, xev_ctx cs μ pre post u v hpre hB, E, map_add,
      map_smul, map_smul, plcL_comp, plcL_oddBubble hi, xev_ctx cs μ pre post u v hpre hC]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul,
      Category.assoc]
    rw [hq, Linear.comp_smul, Linear.comp_smul, smul_smul, mul_comm]
  · refine ⟨0, ?_⟩
    rw [xev_ctx cs μ pre post u v hpre hA, xev_ctx cs μ pre post u v hpre hB, E]
    simp only [zero_smul, add_zero, mul_zero, map_smul, Linear.smul_comp, Linear.comp_smul]

/-- **A dot moves over a cap of a matching**, up to sign modulo the diagram without the dot
followed by the odd bubble. -/
theorem dot_cap_leg {ν : X} {s₀ t₀ : List (Letter I)} (v w : List (Letter I)) (y : Letter I)
    (Pre Q : List (XLayer I)) (hP : XChain s₀ Pre (v ++ flipL y :: y :: w)) :
    SignRel (BubTerm cs ν s₀ t₀ (Pre ++ tmLay (v ++ flipL y :: y :: w) (.cap v.length) ++ Q))
      (xev cs ν s₀ t₀ (Pre ++ dotOn (v ++ flipL y :: y :: w) (v.length + 1) ++
        tmLay (v ++ flipL y :: y :: w) (.cap v.length) ++ Q))
      (xev cs ν s₀ t₀ (Pre ++ dotOn (v ++ flipL y :: y :: w) v.length ++
        tmLay (v ++ flipL y :: y :: w) (.cap v.length) ++ Q)) := by
  obtain ⟨hcap, -⟩ := tmLay_cap v w (flipL y) y
  rw [hcap, dotOn_eq' (u := v ++ [flipL y]) (l := y) (w := w) (by simp) (by simp),
    dotOn_eq' (u := v) (l := flipL y) (w := y :: w) rfl rfl]
  obtain ⟨p, r, hir, E⟩ := dotCap (cs := cs) (wt D ν w) y
  obtain ⟨q, hq⟩ := xev_oddBubble_ctx_above (t₀ := t₀) ν Pre Q v w E hir
    (hP.cast rfl (by simp))
    (((xChain_xDotL y).whisk [flipL y] []).append (xChain_xCapL y) |>.cast (by simp) rfl)
    (((xChain_xDotL (flipL y)).whisk [] [y]).append (xChain_xCapL y) |>.cast (by simp) rfl)
    (xChain_xCapL y)
  refine ⟨p, ?_⟩
  have e1 : Pre ++ (xDotL y).map (xwhL (v ++ [flipL y]) w) ++ (xCapL y).map (xwhL v w) ++ Q =
      Pre ++ ((xDotL y).map (xwhL [flipL y] []) ++ xCapL y).map (xwhL v w) ++ Q := by
    simp [List.map_map, Function.comp_def, xwhL]
  have e2 : Pre ++ (xDotL (flipL y)).map (xwhL v (y :: w)) ++ (xCapL y).map (xwhL v w) ++ Q =
      Pre ++ ((xDotL (flipL y)).map (xwhL [] [y]) ++ xCapL y).map (xwhL v w) ++ Q := by
    simp [List.map_map, Function.comp_def, xwhL]
  rw [e1, e2, hq, add_sub_cancel_left]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, IsBubbleProd.of_oddBubble ν y.2, rfl⟩)

/-- **A dot moves around a cup of a matching**, up to sign modulo the diagram without the dot
followed by the odd bubble. -/
theorem dot_cup_leg {ν : X} {s₀ t₀ : List (Letter I)} (v w : List (Letter I)) (a : Letter I)
    (Pre Q : List (XLayer I)) (hP : XChain s₀ Pre (v ++ w)) :
    SignRel (BubTerm cs ν s₀ t₀ (Pre ++ tmLay (v ++ w) (.mv (.cup v.length a)) ++ Q))
      (xev cs ν s₀ t₀ (Pre ++ tmLay (v ++ w) (.mv (.cup v.length a)) ++
        dotOn (tLet (v ++ w) (.mv (.cup v.length a))) (v.length + 1) ++ Q))
      (xev cs ν s₀ t₀ (Pre ++ tmLay (v ++ w) (.mv (.cup v.length a)) ++
        dotOn (tLet (v ++ w) (.mv (.cup v.length a))) v.length ++ Q)) := by
  simp only [tmLay, tLet]
  rw [moveLay_cup, chStep_cup,
    dotOn_eq' (u := v ++ [a]) (l := flipL a) (w := w) (by simp) (by simp), dotOn_eq]
  obtain ⟨p, r', hir, E⟩ := dotCup (cs := cs) (wt D ν w) a
  obtain ⟨q, hq⟩ := xev_oddBubble_ctx (t₀ := t₀) ν Pre Q v w E hir (hP.cast rfl (by simp))
    ((xChain_xCupL a).app ((xChain_xDotL (flipL a)).whisk [a] []) (by simp) |>.cast rfl
      (by simp))
    ((xChain_xCupL a).app ((xChain_xDotL a).whisk [] [flipL a]) (by simp) |>.cast rfl
      (by simp))
    (xChain_xCupL a)
  refine ⟨p, ?_⟩
  have e1 : Pre ++ (xCupL a).map (xwhL v w) ++ (xDotL (flipL a)).map (xwhL (v ++ [a]) w) ++ Q =
      Pre ++ (xCupL a ++ (xDotL (flipL a)).map (xwhL [a] [])).map (xwhL v w) ++ Q := by
    simp
  have e2 : Pre ++ (xCupL a).map (xwhL v w) ++ (xDotL a).map (xwhL v (flipL a :: w)) ++ Q =
      Pre ++ (xCupL a ++ (xDotL a).map (xwhL [] [flipL a])).map (xwhL v w) ++ Q := by
    simp
  rw [e1, e2, hq, add_sub_cancel_left]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, IsBubbleProd.of_oddBubble ν a.2, rfl⟩)

end DotPass

/-! ## Dots slide along the arcs of a decorated matching -/

section Arcs

open DTMove

theorem ncr₂_append (R R' : List (TMove (Letter I))) : ncr₂ (R ++ R') = ncr₂ R + ncr₂ R' := by
  simp only [Chord.ncr₂, List.countP_append]

variable (cs) in
/-- **The base of a matching**: a one-sided diagram `B₀ : 1 → E_{l₀}` whose pairing is the state
`T₀`, along whose arcs dots slide, up to sign modulo lower terms and terms with the odd bubble and
one dot fewer. -/
structure DotBase (μ : X) (T₀ : TState (Letter I)) (l₀ : List (Letter I))
    (B₀ : List (XLayer I)) : Prop where
  inv : TInv T₀
  letters : T₀.st.map Prod.snd = l₀
  chain : XChain [] B₀ l₀
  arc : ∀ {p e : ℕ}, Same T₀.st p e → ∀ (Q : List (XLayer I)) (t₀ : List (Letter I)),
    SignRel (LtL D Sc cs μ [] t₀ (xcnt B₀ + xcnt Q) ⊔ BubTerm cs μ [] t₀ (B₀ ++ Q))
      (xev cs μ [] t₀ (B₀ ++ dotOn l₀ p ++ Q)) (xev cs μ [] t₀ (B₀ ++ dotOn l₀ e ++ Q))

variable {μ : X} {T₀ : TState (Letter I)} {l₀ : List (Letter I)} {B₀ : List (XLayer I)}

/-- **A dot slides along an arc of a decorated matching** (from one end at the top to the other),
up to sign modulo lower terms and the diagram without the dot followed by the odd bubble. -/
theorem DotBase.arc_dot (hB : DotBase cs μ T₀ l₀ B₀) : ∀ (ds : List (DTMove I)),
    TFits flipL 0 T₀ (tmoves ds) → ∀ {p e : ℕ}, Same (tRun flipL 0 T₀ (tmoves ds)).st p e →
    ∀ (Q : List (XLayer I)) (t₀ : List (Letter I)),
    SignRel (LtL D Sc cs μ [] t₀ (xcnt B₀ + ncr₂ (tmoves ds) + xcnt Q) ⊔
        BubTerm cs μ [] t₀ (B₀ ++ dLay l₀ ds ++ Q))
      (xev cs μ [] t₀ (B₀ ++ dLay l₀ ds ++ dotOn ((tmoves ds).foldl tLet l₀) p ++ Q))
      (xev cs μ [] t₀ (B₀ ++ dLay l₀ ds ++ dotOn ((tmoves ds).foldl tLet l₀) e ++ Q)) := by
  intro ds
  induction ds using List.reverseRecOn with
  | nil =>
    intro _ p e hs Q t₀
    simpa [dLay, tmoves, Chord.ncr₂] using hB.arc hs Q t₀
  | append_singleton ds x ih =>
    intro hf p e hs Q t₀
    set T := tRun flipL 0 T₀ (tmoves ds) with hT
    set l := (tmoves ds).foldl tLet l₀ with hl
    set Pre := B₀ ++ dLay l₀ ds with hPre
    rcases x with m | i
    · -- a move
      rw [tmoves_append, tmoves_tm, tFits_append] at hf
      obtain ⟨hf1, hm, -⟩ := hf
      obtain ⟨hlT, hch, hx⟩ := dLay_spec ds hB.letters hf1
      rw [← hT, ← hl] at hlT
      rw [← hl] at hch
      rw [← hT] at hm
      have hP : XChain [] Pre l := hB.chain.append hch
      have hL : LOk l m := lOk_of_ok hlT hm
      have hlen : T.st.length = l.length := by rw [← hlT, List.length_map]
      rw [tmoves_append, tmoves_tm, tRun_snoc, ← hT] at hs
      set M := tmLay l m with hM
      set S := LtL D Sc cs μ [] t₀ (xcnt B₀ + ncr₂ (tmoves ds) + ncr₂ [m] + xcnt Q) ⊔
        BubTerm cs μ [] t₀ (Pre ++ M ++ Q) with hS
      set F : ℕ → _ := fun x => xev cs μ [] t₀ (Pre ++ M ++ dotOn (tLet l m) x ++ Q) with hF
      set G : ℕ → _ := fun y => xev cs μ [] t₀ (Pre ++ dotOn l y ++ M ++ Q) with hG
      suffices SignRel S (F p) (F e) by
        simpa [F, S, Pre, M, l, dLay_append, dLay, ncr₂_append, List.append_assoc,
          Nat.add_assoc] using this
      have hGG : ∀ {y y'}, Same T.st y y' → SignRel S (G y) (G y') := by
        intro y y' hyy
        have := ih hf1 hyy (M ++ Q) t₀
        simp only [xcnt_append, hM, ← List.append_assoc] at this
        refine this.mono (sup_le_sup ?_ le_rfl)
        rw [hx] at *
        exact ltL_mono (by rw [show xcnt (tmLay l m) = ncr₂ [m] from (tStep_spec hlT hm).2.2]; omega)
      have hpass : ∀ y, y < T.st.length → ¬ CapLeg m y → SignRel S (G y) (F (tPos m y)) := by
        intro y hy hym
        have := dot_tm_pass (cs := cs) (ν := μ) (t₀ := t₀) hL (by omega) hym Pre Q hP
        rw [xcnt_append, hx] at this
        exact this.signRel.mono le_sup_left
      rcases m with (⟨g, a⟩ | q) | g
      · -- a cup
        have hg : g ≤ T.st.length := by have := hm; simp only [TMove.Ok] at this; omega
        have hk : ∀ x ∈ T.st, x.1 ≠ T.nxt := fun x hx => ((hB.inv.run hf1).fresh x hx).ne
        simp only [Chord.tStep, zero_add] at hs
        rw [Chord.same_insAt_iff hg hk] at hs
        obtain ⟨v, w, hvw, hv⟩ := exists_split_cup (l := l) (g := g) (by omega)
        have hcup := dot_cup_leg (cs := cs) (ν := μ) (t₀ := t₀) v w a Pre Q (hvw ▸ hP)
        rw [← hvw, hv] at hcup
        rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2, h3, h4, h5⟩
        · exact (hcup.mono le_sup_right).symm
        · exact hcup.mono le_sup_right
        · have hmp : ∀ x, x ≠ g → x ≠ g + 1 →
              tPos (.mv (.cup g a)) (if x < g then x else x - 2) = x := by
            intro x hx1 hx2; simp only [tPos, movePos]; split_ifs <;> omega
          have hp := hpass _ h5.lt_left (fun h => h)
          have he := hpass _ h5.lt_right (fun h => h)
          rw [hmp p h1 h2] at hp
          rw [hmp e h3 h4] at he
          exact hp.symm.trans ((hGG h5).trans he)
      · -- a crossing
        have hq : q + 1 < T.st.length := by have := hm; simp only [TMove.Ok] at this; omega
        simp only [Chord.tStep, zero_add] at hs
        rw [Chord.same_swapAt hq] at hs
        have hmp : ∀ x, tPos (I := I) (.mv (.cross q)) (Chord.tau q x) = x :=
          fun x => Chord.tau_tau q x
        have hp := hpass _ hs.lt_left (fun h => h)
        have he := hpass _ hs.lt_right (fun h => h)
        rw [hmp] at hp he
        exact hp.symm.trans ((hGG hs).trans he)
      · -- a cap
        obtain ⟨A, B, hA, hB', -, -⟩ := hm
        simp only [zero_add] at hA hB'
        have hr : g + 1 < T.st.length := by
          by_contra h; rw [List.getElem?_eq_none (by omega)] at hB'; cases hB'
        simp only [Chord.tStep, zero_add] at hs
        rw [Chord.same_jn_iff hr] at hs
        obtain ⟨-, -, -, hs⟩ := hs
        have hmp : ∀ x, tPos (I := I) (.cap g) (Chord.rmIdx g x) = x := by
          intro x; simp only [tPos, Chord.rmIdx]; split_ifs <;> omega
        have hnl : ∀ x, ¬ CapLeg (I := I) (.cap g) (Chord.rmIdx g x) := by
          intro x h; simp only [CapLeg, Chord.rmIdx] at h; split_ifs at h <;> omega
        obtain ⟨v, y, w, hvw, hv⟩ := hL
        have hcap := dot_cap_leg (cs := cs) (ν := μ) (t₀ := t₀) v w y Pre Q (hvw ▸ hP)
        rw [← hvw, hv] at hcap
        have hcap' : SignRel S (G (g + 1)) (G g) := hcap.mono le_sup_right
        rcases hs with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hp := hpass _ h.lt_left (hnl p)
          have he := hpass _ h.lt_right (hnl e)
          rw [hmp] at hp he
          exact hp.symm.trans ((hGG h).trans he)
        · have hp := hpass _ h1.lt_left (hnl p)
          have he := hpass _ h2.lt_left (hnl e)
          rw [hmp] at hp he
          exact hp.symm.trans ((hGG h1).trans (hcap'.trans ((hGG h2.symm).trans he)))
        · have hp := hpass _ h1.lt_left (hnl p)
          have he := hpass _ h2.lt_left (hnl e)
          rw [hmp] at hp he
          exact hp.symm.trans ((hGG h1).trans (hcap'.symm.trans ((hGG h2.symm).trans he)))
    · -- a dot
      rw [tmoves_append, tmoves_dt, List.append_nil] at hf hs ⊢
      obtain ⟨hlT, hch, hx⟩ := dLay_spec ds hB.letters hf
      rw [← hT, ← hl] at hlT
      rw [← hl] at hch
      rw [← hT] at hs
      have hP : XChain [] Pre l := hB.chain.append hch
      have hlen : T.st.length = l.length := by rw [← hlT, List.length_map]
      have hsw : ∀ y, y < l.length → XLt cs μ [] t₀ 0 (Pre ++ dotOn l i ++ dotOn l y ++ Q)
          (Pre ++ dotOn l y ++ dotOn l i ++ Q) := by
        intro y hy
        by_cases hi : i < l.length
        · exact dotOn_comm hi hy Pre Q hP
        · rw [dotOn_of_le (by omega)]; simpa using XLt.refl _
      set S := LtL D Sc cs μ [] t₀ (xcnt B₀ + ncr₂ (tmoves ds) + xcnt Q) ⊔
        BubTerm cs μ [] t₀ (Pre ++ dotOn l i ++ Q) with hS
      suffices SignRel S (xev cs μ [] t₀ (Pre ++ dotOn l i ++ dotOn l p ++ Q))
          (xev cs μ [] t₀ (Pre ++ dotOn l i ++ dotOn l e ++ Q)) by
        simpa [S, Pre, l, dLay_append, dLay, List.append_assoc] using this
      have H := ih hf hs (dotOn l i ++ Q) t₀
      rw [xcnt_append, xcnt_dotOn, zero_add] at H
      simp only [← List.append_assoc] at H
      have h1 : SignRel S _ _ := ((hsw p (by have := hs.lt_left; omega)).mono
        (Nat.zero_le (xcnt B₀ + ncr₂ (tmoves ds) + xcnt Q))).signRel.mono le_sup_left
      have h2 : SignRel S _ _ := ((hsw e (by have := hs.lt_right; omega)).mono
        (Nat.zero_le (xcnt B₀ + ncr₂ (tmoves ds) + xcnt Q))).signRel.mono le_sup_left
      exact h1.trans (H.trans h2.symm)

/-- The renaming of strand ids by a move of a decorated matching. -/
def zRen (T : TState (Letter I)) : DTMove I → ℕ → ℕ
  | .tm m => stepRen 0 T m
  | .dt _ => id

theorem tRen_cons_d (T₀ : TState (Letter I)) (ds : List (DTMove I)) (z : DTMove I)
    (S : List (DTMove I)) (x : ℕ) :
    tRen 0 (tRun flipL 0 T₀ (tmoves (ds ++ [z]))) (tmoves S)
        (zRen (tRun flipL 0 T₀ (tmoves ds)) z x) =
      tRen 0 (tRun flipL 0 T₀ (tmoves ds)) (tmoves (z :: S)) x := by
  rcases z with m | i
  · rw [tmoves_append, tmoves_tm, tRun_snoc]; rfl
  · rw [tmoves_append, tmoves_dt, List.append_nil]; rfl

theorem not_same_capLegs {T : TState (Letter I)} {g : ℕ} (hm : (TMove.cap g).Ok flipL 0 T.st) :
    ¬ Same T.st g (g + 1) := by
  obtain ⟨A, B, hA, hB', -, hne⟩ := hm
  simp only [zero_add] at hA hB'
  intro h
  have := h.2.2
  simp [Chord.idAt, hA, hB'] at this
  exact hne this

theorem idD_eq_of_same {s : List (ℕ × Letter I)} {x e : ℕ} (h : Same s x e) :
    idD s x = idD s e := by
  rw [idD, idD, h.2.2]

/-- **A dot moves up its strand to the top of a decorated matching**, up to sign modulo lower
terms and the diagram without the dot followed by the odd bubble. The strand id at the top is the
id at the start, renamed along the later caps (`tRen`). -/
theorem DotBase.dot_up (hB : DotBase cs μ T₀ l₀ B₀) : ∀ (S ds : List (DTMove I)),
    TFits flipL 0 T₀ (tmoves (ds ++ S)) → ∀ {x : ℕ}, x < (tRun flipL 0 T₀ (tmoves ds)).st.length →
    ∀ (Q : List (XLayer I)) (t₀ : List (Letter I)), ∃ y,
      y < (tRun flipL 0 T₀ (tmoves (ds ++ S))).st.length ∧
      idD (tRun flipL 0 T₀ (tmoves (ds ++ S))).st y =
        tRen 0 (tRun flipL 0 T₀ (tmoves ds)) (tmoves S) (idD (tRun flipL 0 T₀ (tmoves ds)).st x) ∧
      SignRel (LtL D Sc cs μ [] t₀ (xcnt B₀ + ncr₂ (tmoves (ds ++ S)) + xcnt Q) ⊔
          BubTerm cs μ [] t₀ (B₀ ++ dLay l₀ (ds ++ S) ++ Q))
        (xev cs μ [] t₀ (B₀ ++ dLay l₀ ds ++ dotOn ((tmoves ds).foldl tLet l₀) x ++
          dLay ((tmoves ds).foldl tLet l₀) S ++ Q))
        (xev cs μ [] t₀ (B₀ ++ dLay l₀ (ds ++ S) ++
          dotOn ((tmoves (ds ++ S)).foldl tLet l₀) y ++ Q)) := by
  intro S
  induction S with
  | nil =>
    intro ds hf x hx Q t₀
    refine ⟨x, by simpa using hx, by simp [tRen, tmoves], ?_⟩
    simpa [dLay] using SignRel.refl _
  | cons z S ih =>
    intro ds hf x hx Q t₀
    have hf' : TFits flipL 0 T₀ (tmoves ((ds ++ [z]) ++ S)) := by
      simpa [List.append_assoc] using hf
    have e1 : ds ++ z :: S = (ds ++ [z]) ++ S := by simp
    rw [tmoves_append, tFits_append] at hf
    obtain ⟨hf1, hf2⟩ := hf
    obtain ⟨hlT, hch, hx0⟩ := dLay_spec ds hB.letters hf1
    have hlen : (tRun flipL 0 T₀ (tmoves ds)).st.length = ((tmoves ds).foldl tLet l₀).length := by
      rw [← hlT, List.length_map]
    have hP : XChain [] (B₀ ++ dLay l₀ ds) ((tmoves ds).foldl tLet l₀) := hB.chain.append hch
    set T := tRun flipL 0 T₀ (tmoves ds) with hT
    set l := (tmoves ds).foldl tLet l₀ with hl
    -- one step
    obtain ⟨x', hx', hid, hrel⟩ : ∃ x', x' < (tRun flipL 0 T₀ (tmoves (ds ++ [z]))).st.length ∧
        idD (tRun flipL 0 T₀ (tmoves (ds ++ [z]))).st x' = zRen T z (idD T.st x) ∧
        SignRel (LtL D Sc cs μ [] t₀ (xcnt B₀ + ncr₂ (tmoves (ds ++ z :: S)) + xcnt Q) ⊔
            BubTerm cs μ [] t₀ (B₀ ++ dLay l₀ (ds ++ z :: S) ++ Q))
          (xev cs μ [] t₀ (B₀ ++ dLay l₀ ds ++ dotOn l x ++ dLay l (z :: S) ++ Q))
          (xev cs μ [] t₀ (B₀ ++ dLay l₀ (ds ++ [z]) ++
            dotOn ((tmoves (ds ++ [z])).foldl tLet l₀) x' ++
            dLay ((tmoves (ds ++ [z])).foldl tLet l₀) S ++ Q)) := by
      rcases z with m | i
      · have hm := hf2.1
        obtain ⟨hl', hcm, hxm⟩ := tStep_spec hlT hm
        obtain ⟨-, -, hxS⟩ := dLay_spec S hl' hf2.2
        have hL := lOk_of_ok hlT hm
        have eT : tRun flipL 0 T₀ (tmoves (ds ++ [.tm m])) = tStep flipL 0 T m := by
          rw [tmoves_append, tmoves_tm, tRun_snoc]
        have eL : (tmoves (ds ++ [.tm m])).foldl tLet l₀ = tLet l m := by
          rw [tmoves_append, tmoves_tm, List.foldl_append]; rfl
        rw [eT, eL]
        have hstart : B₀ ++ dLay l₀ ds ++ dotOn l x ++ dLay l (.tm m :: S) ++ Q =
            B₀ ++ dLay l₀ ds ++ dotOn l x ++ tmLay l m ++ (dLay (tLet l m) S ++ Q) := by
          simp [dLay]
        have hend : ∀ x', B₀ ++ dLay l₀ (ds ++ [.tm m]) ++ dotOn (tLet l m) x' ++
            dLay (tLet l m) S ++ Q = B₀ ++ dLay l₀ ds ++ tmLay l m ++ dotOn (tLet l m) x' ++
              (dLay (tLet l m) S ++ Q) := by
          intro x'; simp [dLay_append, dLay, ← hl]
        have hbub : B₀ ++ dLay l₀ (ds ++ .tm m :: S) ++ Q =
            B₀ ++ dLay l₀ ds ++ (tmLay l m ++ (dLay (tLet l m) S ++ Q)) := by
          simp [dLay_append, dLay, ← hl]
        have hn : ncr₂ (tmoves (ds ++ .tm m :: S)) =
            ncr₂ (tmoves ds) + ncr₂ [m] + xcnt (dLay (tLet l m) S) := by
          rw [hxS, tmoves_append, tmoves, ncr₂_append, ncr₂_cons]; ring
        simp only [hstart, hend, hbub, hn]
        have hpass : ∀ y, y < T.st.length → ¬ CapLeg m y →
            SignRel (LtL D Sc cs μ [] t₀ (xcnt B₀ + (ncr₂ (tmoves ds) + ncr₂ [m] +
                xcnt (dLay (tLet l m) S)) + xcnt Q) ⊔
              BubTerm cs μ [] t₀ (B₀ ++ dLay l₀ ds ++ (tmLay l m ++ (dLay (tLet l m) S ++ Q))))
            (xev cs μ [] t₀ (B₀ ++ dLay l₀ ds ++ dotOn l y ++ tmLay l m ++
              (dLay (tLet l m) S ++ Q)))
            (xev cs μ [] t₀ (B₀ ++ dLay l₀ ds ++ tmLay l m ++ dotOn (tLet l m) (tPos m y) ++
              (dLay (tLet l m) S ++ Q))) := by
          intro y hy hym
          have := dot_tm_pass (cs := cs) (ν := μ) (t₀ := t₀) hL (by omega) hym
            (B₀ ++ dLay l₀ ds) (dLay (tLet l m) S ++ Q) hP
          exact this.signRel.mono (le_sup_of_le_left (ltL_mono (by
            simp only [xcnt_append, hx0]; omega)))
        by_cases hleg : CapLeg m x
        · obtain ⟨e, he⟩ := (hB.inv.run hf1).valid.exists (show x < T.st.length from hx)
          have hel : ¬ CapLeg m e := by
            rcases m with mm | g
            · exact fun h => h
            · simp only [CapLeg] at hleg ⊢
              have hns := not_same_capLegs hm
              rintro (rfl | rfl) <;> rcases hleg with rfl | rfl
              · exact he.ne rfl
              · exact hns he.symm
              · exact hns he
              · exact he.ne rfl
          have harc := hB.arc_dot ds hf1 he (tmLay l m ++ (dLay (tLet l m) S ++ Q)) t₀
          refine ⟨tPos m e, (idD_tStep hm he.lt_right hel).1, ?_, ?_⟩
          · rw [(idD_tStep hm he.lt_right hel).2, ← idD_eq_of_same he]; rfl
          · refine SignRel.trans ?_ (hpass e he.lt_right hel)
            have harc' : SignRel (LtL D Sc cs μ [] t₀ (xcnt B₀ + (ncr₂ (tmoves ds) + ncr₂ [m] +
                xcnt (dLay (tLet l m) S)) + xcnt Q) ⊔
                  BubTerm cs μ [] t₀ (B₀ ++ dLay l₀ ds ++ (tmLay l m ++ (dLay (tLet l m) S ++ Q))))
                (xev cs μ [] t₀ (B₀ ++ dLay l₀ ds ++ dotOn l x ++ tmLay l m ++
                  (dLay (tLet l m) S ++ Q)))
                (xev cs μ [] t₀ (B₀ ++ dLay l₀ ds ++ dotOn l e ++ tmLay l m ++
                  (dLay (tLet l m) S ++ Q))) := by
              have := harc.mono (sup_le_sup (ltL_mono (le_of_eq (show xcnt B₀ + ncr₂ (tmoves ds) +
                xcnt (tmLay l m ++ (dLay (tLet l m) S ++ Q)) = xcnt B₀ + (ncr₂ (tmoves ds) +
                  ncr₂ [m] + xcnt (dLay (tLet l m) S)) + xcnt Q by
                    simp only [xcnt_append, hxm]; omega))) le_rfl)
              simpa only [List.append_assoc] using this
            exact harc'
        · exact ⟨tPos m x, (idD_tStep hm hx hleg).1, (idD_tStep hm hx hleg).2,
            hpass x hx hleg⟩
      · have eT : tRun flipL 0 T₀ (tmoves (ds ++ [.dt i])) = T := by
          rw [tmoves_append, tmoves_dt, List.append_nil]
        have eL : (tmoves (ds ++ [.dt i])).foldl tLet l₀ = l := by
          rw [tmoves_append, tmoves_dt, List.append_nil]
        rw [eT, eL]
        refine ⟨x, hx, rfl, ?_⟩
        have hsw : XLt cs μ [] t₀ 0 (B₀ ++ dLay l₀ ds ++ dotOn l x ++ dotOn l i ++
            (dLay l S ++ Q)) (B₀ ++ dLay l₀ ds ++ dotOn l i ++ dotOn l x ++ (dLay l S ++ Q)) := by
          by_cases hi : i < l.length
          · exact dotOn_comm (by rw [← hlen]; exact hx) hi _ _ hP
          · rw [dotOn_of_le (t := l) (i := i) (by omega)]; simpa using XLt.refl _
        have := (hsw.mono (Nat.zero_le (xcnt B₀ + ncr₂ (tmoves (ds ++ .dt i :: S)) +
          xcnt Q))).signRel.mono (le_sup_left (b := BubTerm cs μ [] t₀
            (B₀ ++ dLay l₀ (ds ++ .dt i :: S) ++ Q)))
        simpa [dLay, dLay_append, ← hl, List.append_assoc] using this
    obtain ⟨y, hy, hidy, hrel'⟩ := ih (ds ++ [z]) hf' hx' Q t₀
    rw [← e1] at hy hidy hrel'
    refine ⟨y, hy, ?_, hrel.trans ?_⟩
    · rw [hidy, hid, tRen_cons_d]
    · simpa only [← e1] using hrel'

variable (cs) in
/-- **Decorated diagrams with fewer dots**: the decorated matchings `ds` with moves `R`, followed
by dots at the top at the positions `Z` and by a product of bubbles, with fewer than `N` dots in
all (as 2-morphisms into `E_t`, `t` being the top letters). -/
def DecSpan (μ : X) (l₀ : List (Letter I)) (B₀ : List (XLayer I)) (R : List (TMove (Letter I)))
    (t : List (Letter I)) (N : ℕ) :
    Submodule k ((pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ t)) :=
  Submodule.span k {f | ∃ (ds : List (DTMove I)) (Z : List ℕ)
    (β : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])),
      tmoves ds = R ∧ DOk₂ l₀ ds ∧ (∀ z ∈ Z, z < t.length) ∧
      ndots ds + Z.length < N ∧ IsBubbleProd cs μ β ∧
      f = xev cs μ [] t (B₀ ++ dLay l₀ ds ++ dotsOn t Z) ≫ bubAt D Sc μ t β}

/-- The strand ids at the top of the dots of a decorated matching (from the state `T`). -/
def dotIds (T : TState (Letter I)) : List (DTMove I) → List ℕ
  | [] => []
  | .tm m :: ds => dotIds (tStep flipL 0 T m) ds
  | .dt i :: ds => tRen 0 T (tmoves ds) (idD T.st i) :: dotIds T ds

theorem tLay_append (l : List (Letter I)) (R R' : List (TMove (Letter I))) :
    tLay l (R ++ R') = tLay l R ++ tLay (R.foldl tLet l) R' := by
  rw [← dLay_map_tm, List.map_append, dLay_append, tmoves_map_tm, dLay_map_tm, dLay_map_tm]

/-- **All dots of a decorated matching move up to the top**, up to sign modulo lower terms and
decorated diagrams with fewer dots followed by bubbles. The strand ids reached are the ids of the
dots renamed along the later caps (`dotIds`). -/
theorem DotBase.dots_up (hB : DotBase cs μ T₀ l₀ B₀) : ∀ (S : List (DTMove I))
    (P : List (TMove (Letter I))) (Y : List ℕ) (t₀ : List (Letter I)),
    (P ++ tmoves S).foldl tLet l₀ = t₀ → TFits flipL 0 T₀ (P ++ tmoves S) →
    DOk₂ (P.foldl tLet l₀) S → (∀ y ∈ Y, y < t₀.length) →
    ∃ Y' : List ℕ, Y'.length = ndots S ∧
      (∀ y ∈ Y', y < (tRun flipL 0 T₀ (P ++ tmoves S)).st.length) ∧
      (Y'.map (idD (tRun flipL 0 T₀ (P ++ tmoves S)).st)).Perm (dotIds (tRun flipL 0 T₀ P) S) ∧
      SignRel (LtL D Sc cs μ [] t₀ (xcnt B₀ + ncr₂ (P ++ tmoves S)) ⊔
          DecSpan cs μ l₀ B₀ (P ++ tmoves S) t₀ (ndots S + Y.length))
        (xev cs μ [] t₀ (B₀ ++ tLay l₀ P ++ dLay (P.foldl tLet l₀) S ++ dotsOn t₀ Y))
        (xev cs μ [] t₀ (B₀ ++ tLay l₀ (P ++ tmoves S) ++ dotsOn t₀ (Y' ++ Y))) := by
  intro S
  induction S with
  | nil =>
    intro P Y t₀ ht _ _ _
    subst ht
    refine ⟨[], rfl, by simp, by simp [dotIds], ?_⟩
    simpa [dLay, tmoves] using SignRel.refl _
  | cons z S ih =>
    intro P Y t₀ ht hf hok hY
    subst ht
    rcases z with m | i
    · have e : P ++ tmoves (.tm m :: S) = (P ++ [m]) ++ tmoves S := by simp [tmoves]
      rw [e] at hf hY ⊢
      obtain ⟨Y', h1, h2, h3, h4⟩ := ih (P ++ [m]) Y _ rfl hf (by simpa [DOk₂] using hok) hY
      refine ⟨Y', h1, h2, ?_, ?_⟩
      · rw [tRun_snoc] at h3; exact h3
      · have e2 : B₀ ++ tLay l₀ P ++ dLay (P.foldl tLet l₀) (.tm m :: S) =
            B₀ ++ tLay l₀ (P ++ [m]) ++ dLay ((P ++ [m]).foldl tLet l₀) S := by
          simp [dLay, tLay_append, tLay, List.append_assoc]
        rw [e2]
        simpa [ndots] using h4
    · simp only [tmoves] at hf hY ⊢
      obtain ⟨hi, hokS⟩ := hok
      set tF := (P ++ tmoves S).foldl tLet l₀ with htF
      have hfS : TFits flipL 0 T₀ (tmoves (P.map .tm ++ S)) := by simpa using hf
      obtain ⟨hlF, -, -⟩ := dLay_spec (P.map .tm ++ S) hB.letters hfS
      obtain ⟨hlP, -, -⟩ := dLay_spec (P.map .tm) hB.letters
        (by simpa using ((tFits_append _ _ _).1 hf).1)
      simp only [tmoves_append, tmoves_map_tm, List.foldl_append] at hlF hlP
      have hx : i < (tRun flipL 0 T₀ (tmoves (P.map .tm))).st.length := by
        rw [tmoves_map_tm, ← List.length_map (f := Prod.snd), hlP]; exact hi
      obtain ⟨y, hy, hidy, hrel⟩ := hB.dot_up S (P.map .tm) hfS hx (dotsOn tF Y) tF
      simp only [tmoves_append, tmoves_map_tm] at hy hidy hrel
      have hyF : y < tF.length := by
        rw [htF, List.foldl_append, ← hlF, List.length_map]; exact hy
      obtain ⟨Y'', h1, h2, h3, h4⟩ := ih P (y :: Y) _ rfl hf hokS (by
        intro z hz; rcases List.mem_cons.1 hz with rfl | hz
        · exact hyF
        · exact hY z hz)
      refine ⟨Y'' ++ [y], by simp [h1, ndots], ?_, ?_, ?_⟩
      · intro z hz; rcases List.mem_append.1 hz with hz | hz
        · exact h2 z hz
        · rw [List.mem_singleton.1 hz]; exact hy
      · rw [List.map_append, List.map_singleton, dotIds, hidy]
        exact (h3.append_right _).trans (List.perm_append_singleton _ _)
      · have hBub : BubTerm cs μ [] tF (B₀ ++ dLay l₀ (P.map .tm ++ S) ++ dotsOn tF Y) ≤
            DecSpan cs μ l₀ B₀ (P ++ tmoves S) tF (ndots (.dt i :: S) + Y.length) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨β, hβ, rfl⟩
          exact Submodule.subset_span ⟨P.map .tm ++ S, Y, β, by simp,
            (dOk₂_append _ _ _).2 ⟨dOk₂_map_tm _ _, by simpa using hokS⟩, hY,
            by simp [ndots], hβ, rfl⟩
        have hrel' : SignRel (LtL D Sc cs μ [] tF (xcnt B₀ + ncr₂ (P ++ tmoves S)) ⊔
            DecSpan cs μ l₀ B₀ (P ++ tmoves S) tF (ndots (.dt i :: S) + Y.length)) _ _ :=
          hrel.mono (sup_le_sup (le_of_eq (by simp)) hBub)
        have h4' : SignRel (LtL D Sc cs μ [] tF (xcnt B₀ + ncr₂ (P ++ tmoves S)) ⊔
            DecSpan cs μ l₀ B₀ (P ++ tmoves S) tF (ndots (.dt i :: S) + Y.length)) _ _ :=
          h4.mono (sup_le_sup le_rfl (le_of_eq (by simp [ndots]; ring_nf; rfl)))
        have := hrel'.trans (by
          simpa only [dLay_append, dLay_map_tm, tmoves_map_tm, List.append_assoc, dotsOn_cons]
            using h4')
        simpa only [dLay, dLay_map_tm, tmoves_map_tm, List.append_assoc, List.singleton_append]
          using this

end Arcs

/-! ## The base: nested cups -/

section Base

open DTMove

theorem tLay_map_mv : ∀ (l : List (Letter I)) (E : List (Move (Letter I))),
    tLay l (E.map .mv) = chordLay l E
  | _, [] => rfl
  | l, m :: E => by simp only [List.map_cons, tLay, chordLay, tmLay, tLet, tLay_map_mv _ E]

theorem foldl_tLet_map_mv (l : List (Letter I)) (E : List (Move (Letter I))) :
    (E.map .mv).foldl tLet l = E.foldl chStep l := by
  induction E generalizing l with
  | nil => rfl
  | cons m E ih => exact ih _

theorem ncr₂_map_mv : ∀ E : List (Move (Letter I)), ncr₂ (E.map .mv) = ncr E
  | [] => rfl
  | m :: E => by rw [List.map_cons, ncr₂_cons, ncr₂_map_mv E, ncr₂_mv, ← ncr_append]; rfl

/-- **A chord diagram as a matching**: its moves fit, and its state is the state of the chord
diagram up to relabelling the arcs. -/
theorem iso_tRun_map_mv : ∀ (E : List (Move (Letter I))) (T : TState (Letter I))
    (s : List (ℕ × Letter I)), Iso T.st s → (∀ x ∈ T.st, x.1 < T.nxt) →
    (∀ x ∈ s, x.1 < s.length) → Fits s.length E →
    TFits flipL 0 T (E.map .mv) ∧ Iso (tRun flipL 0 T (E.map .mv)).st (E.foldl (Chord.step flipL) s)
  | [], _, _, h, _, _, _ => ⟨trivial, h⟩
  | m :: E, T, s, h, hT, hs, hf => by
    have hlen := h.length_eq
    cases m with
    | cup g a =>
      have hg : g ≤ s.length := hf.1
      have h' := h.insAt (g := g) (by omega) (fun x hx => (hT x hx).ne) (fun x hx => (hs x hx).ne)
        a (flipL a)
      have := iso_tRun_map_mv E (tStep flipL 0 T (.mv (.cup g a))) (Chord.step flipL s (.cup g a))
        (by simpa [Chord.tStep, Chord.step] using h')
        (by
          intro x hx
          simp only [Chord.tStep, zero_add] at hx ⊢
          rcases Chord.mem_insAt hx with hx | rfl | rfl
          · have := hT x hx; omega
          · simp
          · simp)
        (by
          intro x hx
          simp only [Chord.step] at hx
          rw [Chord.length_step]
          rcases Chord.mem_insAt hx with hx | rfl | rfl
          · have := hs x hx; simp only [Move.len]; omega
          · simp [Move.len]
          · simp [Move.len])
        (by rw [Chord.length_step]; exact hf.2)
      exact ⟨⟨show 0 + g ≤ T.st.length by omega, this.1⟩, this.2⟩
    | cross p =>
      have hp : p + 1 < s.length := hf.1
      have := iso_tRun_map_mv E (tStep flipL 0 T (.mv (.cross p))) (Chord.step flipL s (.cross p))
        (by simpa [Chord.tStep, Chord.step] using h.swapAt p)
        (by intro x hx; simp only [Chord.tStep] at hx; exact hT x (Chord.mem_swapAt hx))
        (by
          intro x hx; simp only [Chord.step] at hx
          rw [Chord.length_step]; exact hs x (Chord.mem_swapAt hx))
        (by rw [Chord.length_step]; exact hf.2)
      exact ⟨⟨show 0 + p + 1 < T.st.length by omega, this.1⟩, this.2⟩

variable (cs) in
/-- The empty base. -/
theorem dotBase_nil (μ : X) : DotBase cs μ ⟨0, [], []⟩ [] [] where
  inv := ⟨fun i hi => by simp at hi, fun e he => by simp at he, fun a b _ => by
    simp only [List.count_nil]
    exact iff_of_false (Chord.not_ilv2_of_absent (fun i h => by simp [Chord.idAt] at h))
      (by decide)⟩
  letters := rfl
  chain := rfl
  arc := fun hs => absurd hs.lt_left (by simp)

variable (cs) in
/-- **Dots slide along the nested cups**: the nested cups `cupA a*` bending the bottom boundary
`a` up form a base (`DotBase`) with the state `tStart a`. -/
theorem dotBase_tStart (μ : X) (a : List (Letter I)) :
    DotBase cs μ (tStart a) (dualW a ++ a) (cupA (dualW a)) := by
  obtain ⟨hf₀, hn₀, hc₀, hw₀⟩ := cupMoves_spec (dualW a)
  rw [dualW_dualW] at hw₀
  have hl₀ : (tStart a).st.map Prod.snd = dualW a ++ a := by
    rw [tStart]; dsimp only; rw [← foldl_chStep_eq, hw₀]
  refine ⟨Chord.tInv_start hf₀ hn₀, hl₀, xChain_cupA_dual a, fun {p e} hs Q t₀ => ?_⟩
  set E := cupMoves (dualW a)
  obtain ⟨hfit, hiso⟩ := iso_tRun_map_mv E ⟨0, [], []⟩ [] (Iso.refl _) (by simp) (by simp) hf₀
  have hs' : Same (tRun flipL 0 ⟨0, [], []⟩ (tmoves ((E.map .mv).map .tm))).st p e := by
    rw [tmoves_map_tm]; exact (hiso.2 p e).2 hs
  have H := (dotBase_nil cs μ).arc_dot ((E.map .mv).map .tm) (by rwa [tmoves_map_tm]) hs' Q t₀
  simp only [tmoves_map_tm, dLay_map_tm, tLay_map_mv, foldl_tLet_map_mv, ncr₂_map_mv, hn₀,
    List.nil_append, xcnt_nil, zero_add, hc₀] at H
  rw [hw₀] at H
  simpa using H

end Base

end OddMath.SKM
