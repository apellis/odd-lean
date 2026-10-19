import OddMath.SKM.CapPushLocalGrading

/-!
# Numerical cap-push through a crossing

Supporting the choice-independence step in Brundan–Ellis, arXiv:1701.04133v2,
Theorem 10.3. We retain the cap-push witnesses of `SpanCapTrack`, but replace its
lower-term relation by generator-table degree and parity equality when the
crossing bound is sharp. The local identities are numerical; no grading is
inferred from a span relation or a possibly zero quotient morphism.
-/

namespace OddMath.SKM
open StringDiagrams
open StringDiagrams.Chord (Move Fits run Iso rl rlId mvL mvR rl_of_ne rl_of_eq)
variable {I X : Type*} [AddCommGroup X] (D : Datum I X) (sy : Symmetrizer D)

/-- A cap-push witness, with numerical equality conditional on sharpness of its crossing bound. -/
def NumericCapPushRes (μ : X) (E : List (Move (Letter I))) (P S Q : List (ℕ × Letter I))
    (A B : ℕ × Letter I) : Prop :=
  ∃ E', Fits 0 E' ∧ Iso (run flipL E') ((P ++ S ++ Q).map (rl B.1 A.1)) ∧
    ncr E' ≤ ncr E + S.length ∧
    (ncr E' = ncr E + S.length →
      tableDegree D sy μ (chordLay [] E ++ (capBlk (S.map Prod.snd) B.2 0).map
        (xwhL (P.map Prod.snd) (Q.map Prod.snd))) = tableDegree D sy μ (chordLay [] E') ∧
      xpar D μ (chordLay [] E ++ (capBlk (S.map Prod.snd) B.2 0).map
        (xwhL (P.map Prod.snd) (Q.map Prod.snd))) = xpar D μ (chordLay [] E'))

/-- The numerical cap-push property for every eligible block on a fixed chord diagram. -/
def NumericCapPush (μ : X) (E : List (Move (Letter I))) : Prop :=
  ∀ (P S Q : List (ℕ × Letter I)) (A B : ℕ × Letter I),
    run flipL E = P ++ [A] ++ S ++ [B] ++ Q → A.2 = flipL B.2 → A.1 ≠ B.1 →
      NumericCapPushRes D sy μ E P S Q A B

variable {D sy} {μ : X}

theorem numeric_snoc {E' : List (Move (Letter I))} {T : List (ℕ × Letter I)}
    (hiso : Iso (run flipL E') T) {l : List (Letter I)} (hT : T.map Prod.snd = l)
    {L₀ : List (XLayer I)}
    (h : tableDegree D sy μ L₀ = tableDegree D sy μ (chordLay [] E') ∧
      xpar D μ L₀ = xpar D μ (chordLay [] E'))
    {m : Move (Letter I)} {M : List (XLayer I)} (hM : moveLay l m = M) :
    tableDegree D sy μ (L₀ ++ M) = tableDegree D sy μ (chordLay [] (E' ++ [m])) ∧
      xpar D μ (L₀ ++ M) = xpar D μ (chordLay [] (E' ++ [m])) := by
  rw [chordLay_snoc, hiso.1, hT, hM]
  exact ⟨by simp only [tableDegree_append, h.1], by simp only [xpar_append, h.2]⟩

theorem numericCapPush_cross {E : List (Move (Letter I))} (ih : NumericCapPush D sy μ E)
    (_hfE : Fits 0 E) {p : ℕ} (hp : p + 1 < (run flipL E).length) :
    NumericCapPush D sy μ (E ++ [.cross p]) := by
  intro P S Q A B ht hl hne
  obtain ⟨u, x, y, w, ht₀, hu⟩ := exists_split_cross hp
  have hncr : ncr (E ++ [.cross p]) = ncr E + 1 := by rw [ncr_append]; rfl
  have hlay : chordLay [] (E ++ [.cross p]) =
      chordLay [] E ++ (xCrL x.2 y.2).map (xwhL (u.map Prod.snd) (w.map Prod.snd)) := by
    rw [chordLay_snoc, ht₀]
    exact congrArg _ (moveLay_cross_eq (by simp) (by simp [hu]))
  rw [run_snoc, ht₀] at ht
  change Chord.swapAt (u ++ x :: y :: w) p = _ at ht
  rw [← hu, swapAt_mid] at ht
  unfold NumericCapPushRes
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
    have H := numeric_snoc hiso (l := ((u ++ [x,y] ++ R ++ S ++ Q).map Prod.snd)) (by simp) I
      (m := .cross u.length) (moveLay_cross_eq (u := u.map Prod.snd)
        (x := x.2) (y := y.2) (w := (R ++ S ++ Q).map Prod.snd) (by simp) (by simp))
    obtain ⟨Hd, Hp⟩ := H
    constructor
    · simpa only [tableDegree_append, tableDegree_whisk, tableDegree_cross,
        add_assoc, add_comm, add_left_comm] using Hd
    · simpa only [xpar_append, xpar_map_xwhL, xpar_cross,
        add_assoc, add_comm, add_left_comm] using Hp
  · -- the strand to the left of `A` enters the block
    subst hP hv h1
    obtain ⟨E', hf', hiso, hle, hxl⟩ := ih u (y :: S) Q x B (by rw [ht₀]; simp) hl hne
    refine ⟨E', hf', by simpa using hiso, by nomega, fun h => ?_⟩
    have I := hxl (by nomega)
    have H := tableDegree_xpar_capBlk_enterL0 D sy (wt D μ (Q.map Prod.snd))
      (S.map Prod.snd) y.2 B.2
    have H' := tableDegree_xpar_context D sy μ (chordLay [] E) [] _ _
      (u.map Prod.snd) (Q.map Prod.snd) H.1 H.2
    have H'' : tableDegree D sy μ
        (chordLay [] E ++ (xCrL x.2 y.2).map (xwhL (u.map Prod.snd)
          ((S ++ [B] ++ Q).map Prod.snd)) ++ (capBlk (S.map Prod.snd) B.2 0).map
            (xwhL ((u ++ [y]).map Prod.snd) (Q.map Prod.snd))) =
        tableDegree D sy μ (chordLay [] E ++ (capBlk ((y :: S).map Prod.snd) B.2 0).map
          (xwhL (u.map Prod.snd) (Q.map Prod.snd))) ∧
        xpar D μ
        (chordLay [] E ++ (xCrL x.2 y.2).map (xwhL (u.map Prod.snd)
          ((S ++ [B] ++ Q).map Prod.snd)) ++ (capBlk (S.map Prod.snd) B.2 0).map
            (xwhL ((u ++ [y]).map Prod.snd) (Q.map Prod.snd))) =
        xpar D μ (chordLay [] E ++ (capBlk ((y :: S).map Prod.snd) B.2 0).map
          (xwhL (u.map Prod.snd) (Q.map Prod.snd))) := by
      simpa [hl] using H'
    exact ⟨H''.1.trans I.1, H''.2.trans I.2⟩
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
    have H := numeric_snoc hiso (l := ((P ++ S₁ ++ [x,y] ++ S₂ ++ Q).map Prod.snd)) (by simp) I
      (m := .cross (P.length + S₁.length))
      (moveLay_cross_eq (u := (P ++ S₁).map Prod.snd) (x := x.2) (y := y.2)
        (w := (S₂ ++ Q).map Prod.snd) (by simp) (by simp))
    have J := tableDegree_xpar_capBlk_crossS D sy (wt D μ (Q.map Prod.snd))
      (S₁.map Prod.snd) (S₂.map Prod.snd) x.2 y.2 B.2
    have J' := tableDegree_xpar_context D sy μ (chordLay [] E) [] _ _
      (P.map Prod.snd) (Q.map Prod.snd) J.1 J.2
    constructor
    · refine Eq.trans ?_ H.1
      simpa [hl] using J'.1
    · refine Eq.trans ?_ H.2
      simpa [hl] using J'.2
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
    have he : chordLay [] E ++ (xCrL x.2 y.2).map
        (xwhL ((P ++ [A] ++ S).map Prod.snd) (w.map Prod.snd)) ++
        (capBlk (S.map Prod.snd) y.2 0).map
          (xwhL (P.map Prod.snd) ((x :: w).map Prod.snd)) =
        chordLay [] E ++ (capBlk ((S ++ [x]).map Prod.snd) y.2 0).map
          (xwhL (P.map Prod.snd) (w.map Prod.snd)) := by
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [← capBlk_enterR]
      simp [hl]
    simpa only [he] using I
  · -- a crossing to the right of the block
    subst hQ hu'
    obtain ⟨E', hf', hiso, hle, hxl⟩ := ih P S (R ++ [x, y] ++ w) A B (by rw [ht₀]; simp) hl hne
    refine ⟨E' ++ [.cross (P.length + S.length + R.length)], fits_snoc'.2 ⟨hf', by
        rw [hiso.length_eq]; show _ + 1 < _; simp only [List.length_map, List.length_append,
          List.length_cons, List.length_nil]; omega⟩,
      iso_snoc_cross hiso (f := rl B.1 A.1) (u := P ++ S ++ R) (x := x) (y := y) (w := w) (by lsimp) (by lsimp)
        (by simp; omega), by nomega, fun h => ?_⟩
    have I := hxl (by nomega)
    have H := numeric_snoc hiso (l := ((P ++ S ++ R ++ [x,y] ++ w).map Prod.snd)) (by simp) I
      (m := .cross (P.length + S.length + R.length))
      (moveLay_cross_eq (u := (P ++ S ++ R).map Prod.snd) (x := x.2) (y := y.2)
        (w := w.map Prod.snd) (by simp) (by simp; omega))
    obtain ⟨Hd, Hp⟩ := H
    constructor
    · simp only [tableDegree_append, tableDegree_whisk, tableDegree_cross,
        List.map_append, List.map_cons, List.map_nil,
        wt_append] at Hd ⊢
      rw [wt_pair_swap_table D (wt D μ (w.map Prod.snd)) y.2 x.2]
      linear_combination Hd
    · simpa only [xpar_append, xpar_map_xwhL, xpar_cross,
        add_assoc, add_comm, add_left_comm] using Hp

end OddMath.SKM
