import OddMath.SKM.CupAttachment

/-!
# Numerical table invariance for one-sided chord rewrites

Supporting Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.3, the choice-independence
step: sum the generator table, not a grade inferred from a quotient morphism.
The left-cup/cap entries are checked against the ordinary lists occurring in
`etaPDiagram`/`epsPDiagram`. `tableDegree_diagram` anchors ordinary lists to
`Diagram.degree`. The six existing `Chord.Step` generators, `Rw`, and `Equiv`
preserve this sum and the existing `xpar`, assuming the moves fit the boundary.
The statements allow arbitrary orientations, colours, and rightmost weights.

This is not invariance under Reidemeister II or curl removal, and does not prove
the two-sided cap-push or normalized-family comparison needed for Claim 2.
-/

namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
variable {I X : Type*} [AddCommGroup X] (D : Datum I X) (sy : Symmetrizer D)

def tableDegree (μ : X) (L : List (XLayer I)) : ℤ :=
  (L.map fun x => match x.2.1 with
    | .gen g => gdeg D sy (g, wt D μ x.2.2)
    | .lcup i => sy.d i * (1 - D.h i (wt D μ x.2.2))
    | .lcap i => sy.d i * (1 + D.h i (wt D μ x.2.2))).sum

@[simp] theorem tableDegree_ofL (μ : X) (L : List (LayerData I)) :
    tableDegree D sy μ (L.map ofL) = gsum D sy μ L := by
  simp [tableDegree, gsum, Function.comp_def, ofL]

theorem tableDegree_diagram (μ : X) {s t : List (Letter I)} (L : List (LayerData I))
    (h : SChain s L t) :
    tableDegree D sy μ (L.map ofL) = Diagram.degree (gdeg D sy) (mkD D μ L h) := by
  rw [tableDegree_ofL, degree_gdeg_mkD]

@[simp] theorem tableDegree_append (μ : X) (L M : List (XLayer I)) :
    tableDegree D sy μ (L ++ M) = tableDegree D sy μ L + tableDegree D sy μ M := by
  simp [tableDegree]

@[simp] theorem tableDegree_whisk (μ : X) (u v : List (Letter I)) (L : List (XLayer I)) :
    tableDegree D sy μ (L.map (xwhL u v)) = tableDegree D sy (wt D μ v) L := by
  simp only [tableDegree, List.map_map]
  congr 2
  funext x
  obtain ⟨a, g, b⟩ := x
  cases g <;> simp [xwhL, wt_append]

@[simp] theorem tableDegree_cross (μ : X) (a b : Letter I) :
    tableDegree D sy μ (xCrL a b) =
      if a.1 = b.1 then sy.d a.2 * D.d a.2 b.2 else 0 := by
  obtain ⟨_ | _, i⟩ := a <;> obtain ⟨_ | _, j⟩ := b
  · rw [xCrL, tableDegree_ofL]
    simp [gsum, dcrossL, sigmaL, whL, gdeg, Datum.d_self]
    have h := sy.symm i j
    nlinarith
  · simp [xCrL, tableDegree, gdeg]
  · simp [xCrL]
  · simp [xCrL, tableDegree, gdeg]

@[simp] theorem tableDegree_cup (μ : X) (a : Letter I) :
    tableDegree D sy μ (xCupL a) =
      sy.d a.2 * (1 + if a.1 then -D.h a.2 μ else D.h a.2 μ) := by
  obtain ⟨_ | _, i⟩ := a <;> simp [xCupL, tableDegree, gdeg, sub_eq_add_neg]

@[simp] theorem xpar_cross (μ : X) (a b : Letter I) :
    xpar D μ (xCrL a b) = D.parity a.2 * D.parity b.2 := by
  obtain ⟨_ | _, i⟩ := a <;> obtain ⟨_ | _, j⟩ := b <;>
    simp [xCrL, xpar, xlpar, ofL, dcrossL, sigmaL, whL, Shape.parity,
      mul_comm]

@[simp] theorem xpar_cup (μ : X) (a : Letter I) :
    xpar D μ (xCupL a) = cupPar D μ a := by
  obtain ⟨_ | _, i⟩ := a <;> simp [xCupL, xpar, xlpar, cupPar, Shape.parity]


@[simp] theorem wt_pair_cancel_table (μ : X) (a : Letter I) (w : List (Letter I)) :
    wt D μ (a :: flipL a :: w) = wt D μ w := by
  obtain ⟨_ | _, i⟩ := a <;> simp [wt, sh, flipL]

theorem wt_pair_swap_table (μ : X) (a b : Letter I) (w : List (Letter I)) :
    wt D μ (a :: b :: w) = wt D μ (b :: a :: w) := by
  simp [wt, add_left_comm]

theorem tableDegree_xpar_step (μ : X) {L R : List (Move (Letter I))}
    (hs : Step L R) (l : List (Letter I)) (hL : Fits l.length L) :
    tableDegree D sy μ (chordLay l L) = tableDegree D sy μ (chordLay l R) ∧
      xpar D μ (chordLay l L) = xpar D μ (chordLay l R) := by
  cases hs with
  | @xx p p' h =>
    simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
    obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := l) hL.1
    obtain ⟨M, x', y', w', rfl, hM⟩ := exists_split_cross (l := w) (p := p' - u.length - 2)
      (by simp at hL; omega)
    have e1 : chordLay (u ++ x :: y :: (M ++ x' :: y' :: w')) [.cross u.length, .cross p'] =
        (xCrL x y).map (xwhL u (M ++ x' :: y' :: w')) ++
          (xCrL x' y').map (xwhL (u ++ y :: x :: M) w') := by
      rw [chordLay_pair, moveLay_cross, chStep_cross,
        moveLay_cross_eq (u := u ++ y :: x :: M) (x := x') (y := y') (w := w') (by simp)
        (by simp; omega)]
    have e2 : chordLay (u ++ x :: y :: (M ++ x' :: y' :: w')) [.cross p', .cross u.length] =
        (xCrL x' y').map (xwhL (u ++ x :: y :: M) w') ++
          (xCrL x y).map (xwhL u (M ++ y' :: x' :: w')) := by
      rw [chordLay_pair, moveLay_cross_eq (u := u ++ x :: y :: M) (x := x') (y := y') (w := w')
          (by simp) (by simp; omega),
        chStep_cross_eq (u := u ++ x :: y :: M) (x := x') (y := y') (w := w') (by simp)
          (by simp; omega),
        moveLay_cross_eq (u := u) (x := x) (y := y) (w := M ++ y' :: x' :: w') (by simp) rfl]
    rw [e1, e2]
    constructor
    · simp only [tableDegree_append, tableDegree_whisk, tableDegree_cross]
      ring
    · simp only [xpar_append, xpar_map_xwhL, xpar_cross]
      ring
  | @xuL p g a h =>
    simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
    obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := l) hL.1
    obtain ⟨M, w', rfl, hM⟩ := exists_split_cup (l := w) (g := g - u.length - 2)
      (by simp at hL; omega)
    have e1 : chordLay (u ++ x :: y :: (M ++ w')) [.cross u.length, .cup g a] =
        (xCrL x y).map (xwhL u (M ++ w')) ++ (xCupL a).map (xwhL (u ++ y :: x :: M) w') := by
      rw [chordLay_pair, moveLay_cross, chStep_cross,
        moveLay_cup_eq (u := u ++ y :: x :: M) (w := w') a (by simp) (by simp; omega)]
    have e2 : chordLay (u ++ x :: y :: (M ++ w')) [.cup g a, .cross u.length] =
        (xCupL a).map (xwhL (u ++ x :: y :: M) w') ++
          (xCrL x y).map (xwhL u (M ++ a :: flipL a :: w')) := by
      rw [chordLay_pair, moveLay_cup_eq (u := u ++ x :: y :: M) (w := w') a (by simp)
          (by simp; omega),
        chStep_cup_eq (u := u ++ x :: y :: M) (w := w') a (by simp) (by simp; omega),
        moveLay_cross_eq (u := u) (x := x) (y := y) (w := M ++ a :: flipL a :: w') (by simp) rfl]
    rw [e1, e2]
    constructor
    · simp only [tableDegree_append, tableDegree_whisk, tableDegree_cross, tableDegree_cup]
      ring
    · simp only [xpar_append, xpar_map_xwhL, xpar_cross, xpar_cup]
      ring
  | @xuR p g a h =>
    simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
    obtain ⟨u, w0, rfl, rfl⟩ := exists_split_cup (l := l) (g := g) (by omega)
    obtain ⟨M, x, y, w, rfl, hM⟩ := exists_split_cross (l := w0) (p := p - u.length)
      (by simp at hL; omega)
    have e1 : chordLay (u ++ (M ++ x :: y :: w)) [.cross p, .cup u.length a] =
        (xCrL x y).map (xwhL (u ++ M) w) ++ (xCupL a).map (xwhL u (M ++ y :: x :: w)) := by
      rw [chordLay_pair, moveLay_cross_eq (u := u ++ M) (x := x) (y := y) (w := w) (by simp)
          (by simp; omega),
        chStep_cross_eq (u := u ++ M) (x := x) (y := y) (w := w) (by simp) (by simp; omega),
        moveLay_cup_eq (u := u) (w := M ++ y :: x :: w) a (by simp) rfl]
    have e2 : chordLay (u ++ (M ++ x :: y :: w)) [.cup u.length a, .cross (p + 2)] =
        (xCupL a).map (xwhL u (M ++ x :: y :: w)) ++
          (xCrL x y).map (xwhL (u ++ a :: flipL a :: M) w) := by
      rw [chordLay_pair, moveLay_cup, chStep_cup,
        moveLay_cross_eq (u := u ++ a :: flipL a :: M) (x := x) (y := y) (w := w) (by simp)
          (by simp; omega)]
    rw [e1, e2]
    constructor
    · simp only [tableDegree_append, tableDegree_whisk, tableDegree_cross, tableDegree_cup]
      simp only [wt_append]
      rw [wt_pair_swap_table D μ y x]
      ring
    · simp only [xpar_append, xpar_map_xwhL, xpar_cross, xpar_cup]
      ring
  | @uu g g' a b h =>
    simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
    obtain ⟨u, w0, rfl, rfl⟩ := exists_split_cup (l := l) (g := g') (by omega)
    obtain ⟨M, w, rfl, hM⟩ := exists_split_cup (l := w0) (g := g - u.length)
      (by simp at hL; omega)
    have e1 : chordLay (u ++ (M ++ w)) [.cup g a, .cup u.length b] =
        (xCupL a).map (xwhL (u ++ M) w) ++ (xCupL b).map (xwhL u (M ++ a :: flipL a :: w)) := by
      rw [chordLay_pair, moveLay_cup_eq (u := u ++ M) (w := w) a (by simp) (by simp; omega),
        chStep_cup_eq (u := u ++ M) (w := w) a (by simp) (by simp; omega),
        moveLay_cup_eq (u := u) (w := M ++ a :: flipL a :: w) b (by simp) rfl]
    have e2 : chordLay (u ++ (M ++ w)) [.cup u.length b, .cup (g + 2) a] =
        (xCupL b).map (xwhL u (M ++ w)) ++ (xCupL a).map (xwhL (u ++ b :: flipL b :: M) w) := by
      rw [chordLay_pair, moveLay_cup, chStep_cup,
        moveLay_cup_eq (u := u ++ b :: flipL b :: M) (w := w) a (by simp) (by simp; omega)]
    rw [e1, e2]
    constructor
    · simp only [tableDegree_append, tableDegree_whisk, tableDegree_cup]
      simp only [wt_append, wt_pair_cancel_table]
      ring
    · simp only [xpar_append, xpar_map_xwhL, xpar_cup]
      ring
  | braid p =>
    simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
    obtain ⟨u, x, y, w, rfl, rfl⟩ := exists_split_cross (l := l) (p := p) (by omega)
    obtain ⟨z, Q, rfl⟩ : ∃ z Q, w = z :: Q := by
      match w, hL with
      | z :: Q, _ => exact ⟨z, Q, rfl⟩
      | [], hL => simp at hL
    have e1 : chordLay (u ++ x :: y :: z :: Q) [.cross u.length, .cross (u.length + 1),
        .cross u.length] = (r3L x y z).map (xwhL u Q) := by
      rw [chordLay_triple, moveLay_cross, chStep_cross,
        moveLay_cross_eq (u := u ++ [y]) (x := x) (y := z) (w := Q) (by simp) (by simp),
        chStep_cross_eq (u := u ++ [y]) (x := x) (y := z) (w := Q) (by simp) (by simp),
        moveLay_cross_eq (u := u) (x := y) (y := z) (w := x :: Q) (by simp) rfl]
      simp [r3L]
    have e2 : chordLay (u ++ x :: y :: z :: Q) [.cross (u.length + 1), .cross u.length,
        .cross (u.length + 1)] = (r3R x y z).map (xwhL u Q) := by
      rw [chordLay_triple,
        moveLay_cross_eq (u := u ++ [x]) (x := y) (y := z) (w := Q) (by simp) (by simp),
        chStep_cross_eq (u := u ++ [x]) (x := y) (y := z) (w := Q) (by simp) (by simp),
        moveLay_cross_eq (u := u) (x := x) (y := z) (w := y :: Q) (by simp) rfl,
        chStep_cross_eq (u := u) (x := x) (y := z) (w := y :: Q) (by simp) rfl,
        moveLay_cross_eq (u := u ++ [z]) (x := x) (y := y) (w := Q) (by simp) (by simp)]
      simp [r3R]
    rw [e1, e2]
    constructor
    · simp only [tableDegree_whisk, r3L, r3R, tableDegree_append, tableDegree_cross]
      ring
    · simp only [xpar_map_xwhL, r3L, r3R, xpar_append, xpar_cross]
      ring
  | pitch g a =>
    simp only [Fits, Chord.Move.Ok, Chord.Move.len] at hL
    obtain ⟨u, w, rfl, rfl⟩ := exists_split_cup (l := l) (g := g) (by omega)
    obtain ⟨m, Q, rfl⟩ : ∃ m Q, w = m :: Q := by
      match w, hL with
      | m :: Q, _ => exact ⟨m, Q, rfl⟩
      | [], hL => simp at hL
    have e1 : chordLay (u ++ m :: Q) [.cup u.length a, .cross (u.length + 1)] =
        ((xCupL a).map (xwhL [] [m]) ++ (xCrL (flipL a) m).map (xwhL [a] [])).map
          (xwhL u Q) := by
      rw [chordLay_pair, moveLay_cup, chStep_cup,
        moveLay_cross_eq (u := u ++ [a]) (x := flipL a) (y := m) (w := Q) (by simp) (by simp)]
      simp
    have e2 : chordLay (u ++ m :: Q) [.cup (u.length + 1) a, .cross u.length] =
        ((xCupL a).map (xwhL [m] []) ++ (xCrL m a).map (xwhL [] [flipL a])).map
          (xwhL u Q) := by
      rw [chordLay_pair, moveLay_cup_eq (u := u ++ [m]) (w := Q) a (by simp) (by simp),
        chStep_cup_eq (u := u ++ [m]) (w := Q) a (by simp) (by simp),
        moveLay_cross_eq (u := u) (x := m) (y := a) (w := flipL a :: Q) (by simp) rfl]
      simp
    rw [e1, e2]
    constructor
    · simp only [tableDegree_whisk, tableDegree_append, tableDegree_cross, tableDegree_cup]
      obtain ⟨_ | _, i⟩ := a <;> obtain ⟨_ | _, j⟩ := m <;>
        simp [flipL, wt, sy.symm] <;> ring
    · simp only [xpar_map_xwhL, xpar_append, xpar_cross, xpar_cup]
      simp [flipL, mul_comm]


/-- Numeric degrees of the two branches used by `etaPDiagram`. -/
theorem tableDegree_etaP_source (μ : X) (i : I) :
    tableDegree D sy μ [([], .lcup i, [])] =
      if 0 < D.h i μ then gsum D sy μ (dcupL i (D.h i μ - 1).toNat)
      else gsum D sy μ (etaL i (-D.h i μ).toNat ++ lcrossL i i) := by
  split_ifs with h
  · simp only [tableDegree, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      wt, add_zero, gsum_dcupL]
    rw [Int.toNat_of_nonneg (show 0 ≤ D.h i μ - 1 by omega)]
    ring
  · simp only [tableDegree, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      wt, add_zero, gsum_append, gsum_etaL, gsum_lcrossL]
    rw [Int.toNat_of_nonneg (show 0 ≤ -D.h i μ by omega)]
    ring

/-- Numeric degrees of the two branches used by `epsPDiagram`. -/
theorem tableDegree_epsP_source (μ : X) (i : I) :
    tableDegree D sy μ [([], .lcap i, [])] =
      if D.h i μ < 0 then gsum D sy μ (dcapL i (-D.h i μ - 1).toNat)
      else gsum D sy μ (lcrossL i i ++ epsL i (D.h i μ).toNat) := by
  split_ifs with h
  · simp only [tableDegree, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      wt, add_zero, gsum_dcapL]
    rw [Int.toNat_of_nonneg (show 0 ≤ -D.h i μ - 1 by omega)]
    ring
  · simp only [tableDegree, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      wt, add_zero, gsum_append, gsum_epsL, gsum_lcrossL]
    rw [Int.toNat_of_nonneg (show 0 ≤ D.h i μ by omega)]
    ring

/-- An existing contextual rewrite preserves the two numerical table sums. -/
theorem tableDegree_xpar_rw (μ : X) {P Q : List (Move (Letter I))}
    (h : Rw P Q) (l : List (Letter I)) (hf : Fits l.length P) :
    tableDegree D sy μ (chordLay l P) = tableDegree D sy μ (chordLay l Q) ∧
      xpar D μ (chordLay l P) = xpar D μ (chordLay l Q) := by
  obtain ⟨A, B, L, R, hs, rfl, rfl⟩ := h
  have hL : Fits (A.foldl chStep l).length L := by
    rw [Chord.fits_append, Chord.fits_append] at hf
    simpa only [foldl_len_eq] using hf.1.2
  have he := (hs.fits_letters (d := flipL) (A.foldl chStep l)).2 hL
  obtain ⟨hd, hp⟩ := tableDegree_xpar_step D sy μ hs _ hL
  simp only [chordLay_append, List.foldl_append, ← he, tableDegree_append, xpar_append]
  exact ⟨by rw [hd], by rw [hp]⟩

/-- Existing one-sided chord equivalence preserves degree and parity on fitting diagrams. -/
theorem tableDegree_xpar_equiv (μ : X) {P Q : List (Move (Letter I))}
    (h : Chord.Equiv P Q) (l : List (Letter I)) (hf : Fits l.length P) :
    tableDegree D sy μ (chordLay l P) = tableDegree D sy μ (chordLay l Q) ∧
      xpar D μ (chordLay l P) = xpar D μ (chordLay l Q) := by
  induction h with
  | rel P Q h => exact tableDegree_xpar_rw D sy μ h l hf
  | refl P => exact ⟨rfl, rfl⟩
  | symm P Q h ih =>
    have hf' := ((Chord.Equiv.fits_letters (d := flipL) h l).1).2 hf
    obtain ⟨hd, hp⟩ := ih hf'
    exact ⟨hd.symm, hp.symm⟩
  | trans P Q R h h' ih ih' =>
    have hf' := ((Chord.Equiv.fits_letters (d := flipL) h l).1).1 hf
    obtain ⟨hd, hp⟩ := ih hf
    obtain ⟨hd', hp'⟩ := ih' hf'
    exact ⟨hd.trans hd', hp.trans hp'⟩


end OddMath.SKM
