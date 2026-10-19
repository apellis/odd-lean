import OddMath.SKM.TwoSidedGrading

/-! Boundary-crossing normalization for Brundan–Ellis, arXiv:1701.04133v2,
Theorem 10.3 Claim 4, using the adjacent-exchange proof in Khovanov–Lauda,
arXiv:0807.3250v1, §2.2 (the minimal/nonminimal intersection cases).

After bending, noninterleaving endpoints admit a minimal appended crossing.
For interleaving endpoints the reverse appended crossing is minimal instead;
existing planar chord equivalence exposes the old intersection at the boundary.
Reversing its degree/parity equation cancels the opposite-oriented bigon.
Only reduced diagrams enter the bent comparison. No general Reidemeister-II
invariance or sharp crossing count for a nonminimal attachment is assumed. -/
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
variable {I X : Type*} [AddCommGroup X]

/-- In the noninterleaving case the appended crossing is already minimal.
The comparison uses only the existing planar moves between reduced diagrams. -/
theorem canon_cross_noninterleaving (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered flipL s)
    (a b : List (Letter I)) (x y : Letter I)
    (hs : s.map Prod.snd = a ++ x :: y :: b)
    (hn : ¬ Same s a.length (a.length + 1)) (hi : ¬ Ilv s a.length) :
    tableDegree D sy μ (chordLay [] (canon (swapAt s a.length))) =
      tableDegree D sy μ (chordLay [] (canon s)) +
        tableDegree D sy (wt D μ b) (xCrL x y) ∧
    xpar D μ (chordLay [] (canon (swapAt s a.length))) =
      xpar D μ (chordLay [] (canon s)) + D.parity x.2 * D.parity y.2 := by
  have hp : a.length + 1 < s.length := by
    have h := congrArg List.length hs
    simp only [List.length_map, List.length_append, List.length_cons] at h
    omega
  obtain ⟨hf, _, hc⟩ := reduced_canon flipL hv hl
  have hiso := (run_canon (d := flipL) _ (Nat.lt_succ_self _) hv hl).2
  have hm : (Move.cross (α := Letter I) a.length).Ok (run flipL (canon s)).length := by
    change a.length + 1 < _
    rw [hiso.length_eq]
    exact hp
  have hfit := fits_snoc'.2 ⟨hf, hm⟩
  have hsw : Iso (run flipL (canon s ++ [.cross a.length])) (swapAt s a.length) := by
    rw [run_snoc]
    exact hiso.swapAt _
  have hcr := cr_swapAt_of_not_ilv hv hp hn hi
  have hred : Chord.Reduced flipL (canon s ++ [.cross a.length]) := by
    apply (reduced_iff flipL hfit).2
    have he := le_antisymm (cr_le_of_iso hsw) (cr_le_of_iso hsw.symm)
    simpa only [ncr_append, ncr_cons_cross, ncr_nil, zero_add, hc, he] using hcr.symm
  have H := tableDegree_xpar_equiv D sy μ (equiv_canon_of_reduced flipL hfit hred) [] hfit
  rw [canon_eq_of_iso hsw, chordLay_snoc, hiso.1, hs, moveLay_cross] at H
  simpa only [tableDegree_append, tableDegree_whisk, xpar_append, xpar_map_xwhL,
    xpar_cross] using And.intro H.1.symm H.2.symm

private theorem not_same_of_boundary_colours
    {s : List (ℕ × Letter I)} (hl : Lettered flipL s)
    (a b : List (Letter I)) (x y : Letter I)
    (hs : s.map Prod.snd = a ++ x :: y :: b) (hc : x.2 ≠ y.2) :
    ¬ Same s a.length (a.length + 1) := by
  intro hn
  have he := hl a.length (a.length + 1) hn (by omega)
  have hx : (s[a.length]?).map Prod.snd = some x := by
    rw [← List.getElem?_map, hs]
    simp
  have hy : (s[a.length + 1]?).map Prod.snd = some y := by
    rw [← List.getElem?_map, hs]
    simp
  rw [hy, ← Option.map_map, hx] at he
  have e : y = flipL x := Option.some.inj he
  exact hc (congrArg Prod.snd e).symm

/-- Both intersection cases. In the interleaving case, the swapped pairing
is noninterleaving. Its minimal diagram followed by the reverse crossing
is planar-equivalent to the original minimal diagram. Thus the unique old
intersection is exposed at the boundary; no nonminimal cap-push is used. -/
theorem canon_opposite_boundary_degree_parity (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered flipL s)
    (a b : List (Letter I)) (x y : Letter I)
    (hs : s.map Prod.snd = a ++ x :: y :: b)
    (hc : x.2 ≠ y.2) (ho : x.1 ≠ y.1) :
    tableDegree D sy μ (chordLay [] (canon (swapAt s a.length))) =
      tableDegree D sy μ (chordLay [] (canon s)) ∧
    xpar D μ (chordLay [] (canon (swapAt s a.length))) =
      xpar D μ (chordLay [] (canon s)) + D.parity x.2 * D.parity y.2 := by
  classical
  have hn := not_same_of_boundary_colours hl a b x y hs hc
  by_cases hi : Ilv s a.length
  · have hp : a.length + 1 < s.length := hi.lt
    have hs' : (swapAt s a.length).map Prod.snd = a ++ y :: x :: b := by
      rw [map_swapAt, hs, swapAt_mid]
    have hl' := hl.swapAt_of_involutive flipL_involutive hp
    have hn' := not_same_of_boundary_colours hl' a b y x hs' (Ne.symm hc)
    have hi' : ¬ Ilv (swapAt s a.length) a.length := by
      rw [ilv_swapAt_iff hv hp hn]
      exact not_not_intro hi
    obtain ⟨hd, hpar⟩ := canon_cross_noninterleaving D sy μ
      (hv.swapAt hp) hl' a b y x hs' hn' hi'
    simp only [swapAt_swapAt, tableDegree_cross, Ne.symm ho, ↓reduceIte, add_zero] at hd
    simp only [swapAt_swapAt, mul_comm (D.parity y.2)] at hpar
    refine ⟨hd.symm, ?_⟩
    rw [hpar, add_assoc, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]
  · simpa only [tableDegree_cross, ho, ↓reduceIte, add_zero] using
      canon_cross_noninterleaving D sy μ hv hl a b x y hs hn hi

/-- The common bending cups have equal invariants after an opposite-oriented
adjacent exchange. Symmetrizability cancels the two coroot contributions. -/
theorem cupA_opposite_swap_degree_parity (D : Datum I X) (sy : Symmetrizer D)
    (μ : X) (a b : List (Letter I)) (i j : I) :
    tableDegree D sy μ (cupA (a ++ (true, i) :: (false, j) :: b)) =
      tableDegree D sy μ (cupA (a ++ (false, j) :: (true, i) :: b)) ∧
    xpar D μ (cupA (a ++ (true, i) :: (false, j) :: b)) =
      xpar D μ (cupA (a ++ (false, j) :: (true, i) :: b)) := by
  induction a generalizing μ with
  | nil =>
    constructor
    · have hw : wt D (wt D μ [flipL (true, i)]) [flipL (false, j)] =
          wt D (wt D μ [flipL (false, j)]) [flipL (true, i)] := by
        simp [wt, sh, flipL, add_left_comm]
      simp only [List.nil_append, cupA, tableDegree_append, tableDegree_whisk,
        tableDegree_cup, ↓reduceIte, hw]
      have hsym := sy.symm i j
      simp only [Datum.d] at hsym
      simp only [flipL, Bool.not_true, Bool.not_false, wt_cons, wt_nil, sh,
        Bool.false_eq_true, ↓reduceIte, Datum.h, map_add, map_neg]
      dsimp [Datum.h] at hsym
      nlinarith
    · simp only [xpar_cupA, cupsPar, List.nil_append, List.map_cons, List.sum_cons]
      ac_rfl
  | cons z a ih =>
    simp only [List.cons_append, cupA, tableDegree_append, tableDegree_whisk,
      xpar_append, xpar_map_xwhL]
    exact ⟨congrArg (_ + ·) (ih (wt D μ [flipL z])).1,
      congrArg (_ + ·) (ih μ).2⟩

/-- Reduced unequal-colour boundary-crossing normalization, BE2 v2 Theorem
10.3 Claim 4. The crossing is at `b.length` in the dualized pairing boundary.
Both intersection cases are included, without an assumed normalization or
numerical identity. This is the undecorated numerical step, not the family
coefficient theorem. -/
theorem reduced₂_opposite_boundary_degree_parity (D : Datum I X) (sy : Symmetrizer D)
    (μ : X) (a b : List (Letter I)) (i j : I) (hij : i ≠ j)
    {R S : List (TMove (Letter I))}
    (hR : IsMatching₂ (a ++ (true, i) :: (false, j) :: b) [] R)
    (hrR : Reduced₂ (a ++ (true, i) :: (false, j) :: b) R)
    (hS : IsMatching₂ (a ++ (false, j) :: (true, i) :: b) [] S)
    (hrS : Reduced₂ (a ++ (false, j) :: (true, i) :: b) S)
    (hi : Iso (pairing₂ (a ++ (false, j) :: (true, i) :: b) S)
      (swapAt (pairing₂ (a ++ (true, i) :: (false, j) :: b) R) b.length)) :
    tableDegree D sy μ (tLay (a ++ (false, j) :: (true, i) :: b) S) =
      tableDegree D sy μ (tLay (a ++ (true, i) :: (false, j) :: b) R) ∧
    xpar D μ (tLay (a ++ (false, j) :: (true, i) :: b) S) =
      xpar D μ (tLay (a ++ (true, i) :: (false, j) :: b) R) +
        D.parity i * D.parity j := by
  obtain ⟨hv, hl, hs⟩ := hR.pairing_properties
  have hs' : (pairing₂ (a ++ (true, i) :: (false, j) :: b) R).map Prod.snd =
      dualW b ++ (true, j) :: (false, i) :: dualW a := by
    simpa [dualW_append, List.append_assoc, flipL] using hs
  have H := canon_opposite_boundary_degree_parity D sy μ hv hl
    (dualW b) (dualW a) (true, j) (false, i) hs' (Ne.symm hij) (by simp)
  simp only [length_dualW, ← canon_eq_of_iso hi, mul_comm (D.parity j)] at H
  have HR := reduced₂_bent_degree_parity D sy μ hR hrR
  have HS := reduced₂_bent_degree_parity D sy μ hS hrS
  have HC := cupA_opposite_swap_degree_parity D sy μ (dualW b) (dualW a) j i
  simp only [tableDegree_append, tableDegree_whisk, wt_nil, xpar_append,
    xpar_map_xwhL] at HR HS
  have hcupD : tableDegree D sy μ (cupA (dualW (a ++ (true, i) :: (false, j) :: b))) =
      tableDegree D sy μ (cupA (dualW (a ++ (false, j) :: (true, i) :: b))) := by
    simpa [dualW_append, List.append_assoc, flipL] using HC.1
  have hcupP : xpar D μ (cupA (dualW (a ++ (true, i) :: (false, j) :: b))) =
      xpar D μ (cupA (dualW (a ++ (false, j) :: (true, i) :: b))) := by
    simpa [dualW_append, List.append_assoc, flipL] using HC.2
  constructor
  · have he := HS.1.trans (H.1.trans HR.1.symm)
    rw [hcupD] at he
    exact add_left_cancel he
  · have he := HS.2.trans (H.2.trans (congrArg (· + D.parity i * D.parity j) HR.2.symm))
    rw [hcupP, add_assoc] at he
    exact add_left_cancel he

end OddMath.SKM
