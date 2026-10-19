import OddMath.SKM.BoundaryFamilyCoefficients

/-! Numerical boundary exchange for the two non-cap classes in Brundan–Ellis,
arXiv:1701.04133v2, Theorem 10.3 Claim 5. The distinct-strand predicate replaces
unequal colours; the minimal reverse crossing handles the intersecting class.
The cap class and the family-coefficient cancellation are not asserted here. -/
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
variable {I X : Type*} [AddCommGroup X]

/-- Opposite-oriented canonical exchange for distinct strands, including equal colours. -/
theorem canon_opposite_boundary_degree_parity_of_not_same (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered flipL s)
    (a b : List (Letter I)) (x y : Letter I)
    (hs : s.map Prod.snd = a ++ x :: y :: b)
    (hn : ¬ Same s a.length (a.length + 1)) (ho : x.1 ≠ y.1) :
    tableDegree D sy μ (chordLay [] (canon (swapAt s a.length))) =
      tableDegree D sy μ (chordLay [] (canon s)) ∧
    xpar D μ (chordLay [] (canon (swapAt s a.length))) =
      xpar D μ (chordLay [] (canon s)) + D.parity x.2 * D.parity y.2 := by
  classical
  by_cases hi : Ilv s a.length
  · have hp : a.length + 1 < s.length := hi.lt
    have hs' : (swapAt s a.length).map Prod.snd = a ++ y :: x :: b := by
      rw [map_swapAt, hs, swapAt_mid]
    have hl' := hl.swapAt_of_involutive flipL_involutive hp
    have hn' : ¬ Same (swapAt s a.length) a.length (a.length + 1) := by
      intro h
      rw [same_swapAt hp, tau_left, tau_right] at h
      exact hn h.symm
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

/-- Non-cap numerical boundary exchange. Both representatives must be reduced,
and the pairing isomorphism records the actual endpoint transposition. -/
theorem reduced₂_opposite_boundary_degree_parity_of_not_same (D : Datum I X) (sy : Symmetrizer D)
    (μ : X) (a b : List (Letter I)) (i j : I)
    {R S : List (TMove (Letter I))}
    (hR : IsMatching₂ (a ++ (true, i) :: (false, j) :: b) [] R)
    (hrR : Reduced₂ (a ++ (true, i) :: (false, j) :: b) R)
    (hS : IsMatching₂ (a ++ (false, j) :: (true, i) :: b) [] S)
    (hrS : Reduced₂ (a ++ (false, j) :: (true, i) :: b) S)
    (hn : ¬ Same (pairing₂ (a ++ (true, i) :: (false, j) :: b) R)
      b.length (b.length + 1))
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
  have H := canon_opposite_boundary_degree_parity_of_not_same D sy μ hv hl
    (dualW b) (dualW a) (true, j) (false, i) hs' (by simpa only [length_dualW] using hn) (by simp)
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

/-- At equal colour the parity shift is the parity of that colour. -/
theorem reduced₂_same_colour_boundary_degree_parity (D : Datum I X) (sy : Symmetrizer D)
    (μ : X) (a b : List (Letter I)) (i : I)
    {R S : List (TMove (Letter I))}
    (hR : IsMatching₂ (a ++ (true, i) :: (false, i) :: b) [] R)
    (hrR : Reduced₂ (a ++ (true, i) :: (false, i) :: b) R)
    (hS : IsMatching₂ (a ++ (false, i) :: (true, i) :: b) [] S)
    (hrS : Reduced₂ (a ++ (false, i) :: (true, i) :: b) S)
    (hn : ¬ Same (pairing₂ (a ++ (true, i) :: (false, i) :: b) R)
      b.length (b.length + 1))
    (hi : Iso (pairing₂ (a ++ (false, i) :: (true, i) :: b) S)
      (swapAt (pairing₂ (a ++ (true, i) :: (false, i) :: b) R) b.length)) :
    tableDegree D sy μ (tLay (a ++ (false, i) :: (true, i) :: b) S) =
      tableDegree D sy μ (tLay (a ++ (true, i) :: (false, i) :: b) R) ∧
    xpar D μ (tLay (a ++ (false, i) :: (true, i) :: b) S) =
      xpar D μ (tLay (a ++ (true, i) :: (false, i) :: b) R) +
        D.parity i := by
  have H := reduced₂_opposite_boundary_degree_parity_of_not_same D sy μ a b i i
    hR hrR hS hrS hn hi
  have hp : D.parity i * D.parity i = D.parity i := by
    generalize D.parity i = e
    fin_cases e <;> rfl
  simpa only [hp] using H

end OddMath.SKM
