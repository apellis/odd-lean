/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.TwoSidedGrading

/-! Undecorated cap-class normalization for Brundan–Ellis, arXiv:1701.04133v2,
Theorem 10.3 Claim 5. The comparison uses reduced representatives and the
pairing obtained by deleting the distinguished adjacent arc. -/
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
variable {I X : Type*} [AddCommGroup X]

/-- Expose the distinguished adjacent arc as the last canonical cup. -/
theorem canon_cap_degree_parity (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {s : List (ℕ × Letter I)} (hv : Valid s) (hl : Lettered flipL s)
    (a b : List (Letter I)) (x : Letter I)
    (hs : s.map Prod.snd = a ++ x :: flipL x :: b)
    (hc : Same s a.length (a.length + 1)) :
    tableDegree D sy μ (chordLay [] (canon s)) =
      tableDegree D sy μ (chordLay [] (canon (rmAt s a.length))) +
        tableDegree D sy (wt D μ b) (xCupL x) ∧
    xpar D μ (chordLay [] (canon s)) =
      xpar D μ (chordLay [] (canon (rmAt s a.length))) + cupPar D μ x := by
  have he : (s[a.length]'hc.lt_left).2 = x := by
    have h := congrArg (fun l => l[a.length]?) hs
    simpa only [List.getElem?_map, List.getElem?_eq_getElem hc.lt_left,
      Option.map_some, List.getElem?_append_right (le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] using h
  have hd : (rmAt s a.length).map Prod.snd = a ++ b := by
    rw [map_rmAt, hs]
    simp [rmAt]
  have hf := (reduced_canon flipL hv hl).1
  have hrun := (run_canon (d := flipL) _ (Nat.lt_succ_self _) (hv.rmAt hc)
    (hl.rmAt hc.lt_right)).2.1
  rw [hd] at hrun
  have H := tableDegree_xpar_equiv D sy μ (canon_cup hv hc) [] hf
  rw [he, chordLay_snoc, hrun, moveLay_cup] at H
  simpa only [tableDegree_append, tableDegree_whisk, xpar_append,
    xpar_map_xwhL, xpar_cup] using H

/-- The inserted opposite letters cancel in bending degree, but not parity. -/
theorem cupA_cap_degree_parity (D : Datum I X) (sy : Symmetrizer D)
    (μ : X) (a b : List (Letter I)) (ε : Bool) (i : I) :
    tableDegree D sy μ (cupA (a ++ (ε, i) :: (!ε, i) :: b)) =
      tableDegree D sy μ (cupA (a ++ b)) ∧
    xpar D μ (cupA (a ++ (ε, i) :: (!ε, i) :: b)) =
      xpar D μ (cupA (a ++ b)) + cupPar D μ (ε, i) + cupPar D μ (!ε, i) := by
  induction a generalizing μ with
  | nil =>
    constructor
    · cases ε <;>
        simp [cupA, tableDegree_append, tableDegree_whisk, tableDegree_cup,
          flipL, wt, sh, Datum.α, D.cd.coroot_root_self] <;> ring
    · simp only [List.nil_append, xpar_cupA, cupsPar_cons]
      abel
  | cons z a ih =>
    simp only [List.cons_append, cupA, tableDegree_append, tableDegree_whisk,
      xpar_append, xpar_map_xwhL]
    refine ⟨congrArg (_ + ·) (ih (wt D μ [flipL z])).1, ?_⟩
    rw [(ih μ).2]
    abel

/-- The canonical shorter boundary identifies its left dual region with the
physical suffix region. No weight equality is an additional premise. -/
private theorem cap_suffix_weight (D : Datum I X) (μ : X)
    (a b : List (Letter I)) {S : List (TMove (Letter I))}
    (hS : IsMatching₂ (a ++ b) [] S) : wt D μ (dualW a) = wt D μ b := by
  obtain ⟨hv, hl, hs⟩ := hS.pairing_properties
  have hf := (reduced_canon flipL hv hl).1
  have hr := (run_canon (d := flipL) _ (Nat.lt_succ_self _) hv hl).2.1
  have hw := (xChain_run hf).wt_eq (D := D) μ
  rw [hr, hs] at hw
  simp only [List.append_nil, dualW_append, wt_append, wt_nil] at hw
  have hc := (xChain_cupA b).wt_eq (D := D) (wt D μ (dualW a))
  simp only [wt_nil, wt_append] at hc
  rw [← hw] at hc
  exact hc

/-- Both cap orientations relative to the deleted shorter reduced matching.
The cap is evaluated at the physical suffix weight, not the exterior weight. -/
theorem reduced₂_cap_degree_parity (D : Datum I X) (sy : Symmetrizer D)
    (μ : X) (a b : List (Letter I)) (ε : Bool) (i : I)
    {R S : List (TMove (Letter I))}
    (hR : IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R)
    (hrR : Reduced₂ (a ++ (ε, i) :: (!ε, i) :: b) R)
    (hS : IsMatching₂ (a ++ b) [] S) (hrS : Reduced₂ (a ++ b) S)
    (hc : Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1))
    (hi : Iso (pairing₂ (a ++ b) S)
      (rmAt (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length)) :
    tableDegree D sy μ (tLay (a ++ (ε, i) :: (!ε, i) :: b) R) =
      tableDegree D sy μ (tLay (a ++ b) S) +
        sy.d i * (1 + if !ε then D.h i (wt D μ b) else -D.h i (wt D μ b)) ∧
    xpar D μ (tLay (a ++ (ε, i) :: (!ε, i) :: b) R) =
      xpar D μ (tLay (a ++ b) S) + cupPar D (wt D μ b) (!ε, i) := by
  obtain ⟨hv, hl, hs⟩ := hR.pairing_properties
  have hs' : (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R).map Prod.snd =
      dualW b ++ (ε, i) :: flipL (ε, i) :: dualW a := by
    simpa [dualW_append, List.append_assoc, flipL] using hs
  have H := canon_cap_degree_parity D sy μ hv hl (dualW b) (dualW a)
    (ε, i) hs' (by simpa only [length_dualW] using hc)
  simp only [length_dualW, ← canon_eq_of_iso hi, tableDegree_cup,
    cap_suffix_weight D μ a b hS] at H
  have HR := reduced₂_bent_degree_parity D sy μ hR hrR
  have HS := reduced₂_bent_degree_parity D sy μ hS hrS
  have HC := cupA_cap_degree_parity D sy μ (dualW b) (dualW a) ε i
  have hd : tableDegree D sy μ (cupA (dualW (a ++ (ε, i) :: (!ε, i) :: b))) =
      tableDegree D sy μ (cupA (dualW (a ++ b))) := by
    simpa [dualW_append, List.append_assoc, flipL] using HC.1
  have hp : xpar D μ (cupA (dualW (a ++ (ε, i) :: (!ε, i) :: b))) =
      xpar D μ (cupA (dualW (a ++ b))) + cupPar D μ (ε, i) + cupPar D μ (!ε, i) := by
    simpa [dualW_append, List.append_assoc, flipL] using HC.2
  simp only [tableDegree_append, tableDegree_whisk, wt_nil, xpar_append,
    xpar_map_xwhL] at HR HS
  rw [hd] at HR
  rw [hp] at HR
  constructor
  · have he := HR.1.trans H.1
    rw [← HS.1] at he
    cases ε <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at he ⊢ <;> omega
  · rw [cupPar_wt]
    have he := HR.2.trans H.2
    rw [← HS.2] at he
    have hz := CharTwo.add_self_eq_zero (cupPar D μ (!ε, i))
    linear_combination he - hz

end OddMath.SKM
