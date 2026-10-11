/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SameColourBubbleSlides
import OddMath.SKM.BubbleSlides
/-!
# Centrality of the normalized odd bubbles

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Corollary 7.4, (7.15), and the introduction’s odd-bubble centrality assertion.

`oddBubble_slide_up` proves the equality of the actual odd-bubble placements
across every upward generator, using degree one of the same-colour,
connected and scalar-corrected disconnected slides. `oddBubble_slide_down`
is its even right-adjunction mate. These are not consequences merely of the
closed-endomorphism superinterchange law.

`oddBubble_naturality` states the supernatural action on arbitrary homogeneous
2-morphisms between words with matching left boundary weight; its parity is
unrestricted. `oddBubble_naturality_add` gives the inhomogeneous even-plus-odd
formula explicitly. Neither a decomposition theorem nor nondegeneracy of the
presentation is assumed or asserted here.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

theorem bubbleCoeffR_one_odd (i : I) (μ : X) (hi : D.parity i = 1) :
    bubbleCoeffR cs i μ 1 = oddBubble cs i μ := by
  have H := eq_5_7_b cs i μ hi 0
  simp only [mul_zero, zero_add, bubRs_zero, Linear.comp_smul, Category.comp_id] at H
  rw [bubbleCoeffR, Nat.cast_one, H, smul_smul, Units.mul_inv, one_smul]

private theorem bubRs_one_slide_ne (i j : I) (μ : X) (hi : D.parity i = 1) (hij : i ≠ j) :
    rbub j μ (bubRs cs i (wt D μ []) 1) =
      (Sc.t i j : k) • lbub j μ (bubRs cs i (wt D μ [up j]) 1) := by
  by_cases hd : D.d i j = 0
  · exact eq_7_13_corrected cs i j μ hij hd 1
  have hdpos : 0 < D.d i j := lt_of_le_of_ne (D.d_nonneg hij) (Ne.symm hd)
  have he := D.even_d_of_odd hi j
  have hdcast := D.dn_cast hij
  have hdn : 2 ≤ D.dn i j := by rcases he with ⟨a, ha⟩; omega
  rw [eq_7_11_connected cs i j μ hij hdpos,
    bubRs_neg cs i _ (show (1 : ℤ) - D.dn i j < 0 by omega)]
  simp only [lbub, map_zero, Limits.zero_comp, smul_zero, add_zero]
  rw [sum_eq_zero (fun p hp => sum_eq_zero (fun q _ => by
    have hp' := mem_Ioo.mp hp
    by_cases ht : (1 : ℤ) + p - D.dn i j < 0
    · rw [bubRs_neg cs i _ ht, map_zero, Limits.zero_comp, smul_zero]
    · have hpval : p + 1 = D.dn i j := by omega
      have hpar : (p : ZMod 2) * D.parity i = 1 := by
        rw [hi, mul_one]
        have hzero : ((D.dn i j : ℕ) : ZMod 2) = 0 := by
          apply ZMod.natCast_eq_zero_iff_even.mpr
          rw [← Int.even_coe_nat]
          simpa only [hdcast] using he
        have H := congrArg (fun a : ℕ => (a : ZMod 2)) hpval
        simp only [Nat.cast_add, Nat.cast_one, hzero] at H
        generalize (p : ZMod 2) = a at H ⊢
        revert a
        decide
      rw [Sc.s_eq_zero i j p q hpar, zero_smul])), add_zero]

/-- Corollary 7.4, upward generator: the actual normalized odd bubble slides. -/
theorem oddBubble_slide_up (i j : I) (μ : X) (hi : D.parity i = 1) :
    rbub j μ (oddBubble cs i (wt D μ [])) =
      lbub j μ (oddBubble cs i (wt D μ [up j])) := by
  by_cases hij : i = j
  · subst j
    have H := eq_7_9 cs i μ hi 1
    simp only [Nat.reduceDiv, zero_add, sum_range_one, Nat.cast_zero, mul_zero,
      zero_add, one_smul, sub_zero, dotsL, List.replicate_zero, cl_nil, Category.comp_id] at H
    rw [← bubbleCoeffR_one_odd cs i _ hi, ← bubbleCoeffR_one_odd cs i _ hi]
    apply (bubbleCoeffR_slide_iff cs i i μ 1).mpr
    simpa only [Sc.t_self, Units.val_one, one_smul] using H
  · rw [← bubbleCoeffR_one_odd cs i _ hi, ← bubbleCoeffR_one_odd cs i _ hi]
    exact (bubbleCoeffR_slide_iff cs i j μ 1).mpr (bubRs_one_slide_ne cs i j μ hi hij)

private def bubbleMate (j : I) (μ : X) :=
  ctxL D Sc μ [dn j] [dn j] [([], Shape.cup j, [dn j])] [dn j] [dn j]
    [([dn j], Shape.cap j, [])] [up j] [up j]

private theorem bubbleMate_cl (j : I) (μ : X) (L : List (LayerData I)) :
    bubbleMate (Sc := Sc) j μ (cl D Sc (wt D μ [dn j]) [up j] [up j] L) =
      cl D Sc μ [dn j] [dn j] (mateL j L) := by
  rw [bubbleMate, ctxL_cl μ (by simp [Shape.dom, Shape.cod]) (by simp [Shape.dom, Shape.cod])]
  rfl

private theorem mate_closed_right (j : I) (μ : X) {L : List (LayerData I)} (hL : SChain [] L []) :
    cl D Sc μ [dn j] [dn j] (mateL j (L.map (whL [up j] []))) =
      cl D Sc μ [dn j] [dn j] (L.map (whL [] [dn j])) := by
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := [dn j]) (T := [dn j])
    [] [([dn j], Shape.cap j, [])]
    (show SChain [] [([], Shape.cup j, [])] [dn j, up j] by simp [Shape.dom, Shape.cod])
    (hL.whisk [] [dn j])
  simp only [parsum_cons, parsum_nil, show (Shape.cup j).parity D = 0 from rfl,
    add_zero, zero_mul, zsign_zero, one_smul] at E
  have hstep := cl_step (D := D) (Sc := Sc) μ (L.map (whL [] [dn j])) [] [] []
    (cl_zigF Sc j μ) (by simpa using hL.whisk [] [dn j]) rfl
    (L := L.map (whL [] [dn j]) ++ [([], Shape.cup j, [dn j]), ([dn j], Shape.cap j, [])])
    (L' := L.map (whL [] [dn j])) (by simp [whL]) (by simp)
  calc
    _ = cl D Sc μ [dn j] [dn j]
        (L.map (whL [] [dn j]) ++ [([], Shape.cup j, [dn j]), ([dn j], Shape.cap j, [])]) := by
      convert E using 1 <;> simp [mateL, whL, List.map_map, Function.comp_def, List.append_assoc]
      rfl
    _ = _ := hstep

private theorem mate_closed_left (j : I) (μ : X) {L : List (LayerData I)} (hL : SChain [] L []) :
    cl D Sc μ [dn j] [dn j] (mateL j (L.map (whL [] [up j]))) =
      cl D Sc μ [dn j] [dn j] (L.map (whL [dn j] [])) := by
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := [dn j]) (T := [dn j])
    [([], Shape.cup j, [dn j])] [] (hL.whisk [dn j] [])
    (show SChain [up j, dn j] [([], Shape.cap j, [])] [] by simp [Shape.dom, Shape.cod])
  simp only [parsum_cons, parsum_nil, show (Shape.cap j).parity D = 0 from rfl,
    add_zero, mul_zero, zsign_zero, one_smul] at E
  have hstep := cl_step (D := D) (Sc := Sc) μ [] (L.map (whL [dn j] [])) [] []
    (cl_zigF Sc j μ) rfl (by simpa using hL.whisk [dn j] [])
    (L := [([], Shape.cup j, [dn j]), ([dn j], Shape.cap j, [])] ++ L.map (whL [dn j] []))
    (L' := L.map (whL [dn j] [])) (by simp [whL]) (by simp)
  calc
    _ = cl D Sc μ [dn j] [dn j]
        ([([], Shape.cup j, [dn j]), ([dn j], Shape.cap j, [])] ++ L.map (whL [dn j] [])) := by
      convert E using 1 <;> simp [mateL, whL, List.map_map, Function.comp_def, List.append_assoc]
      have hm : whL [dn j] [] = fun x : LayerData I => (dn j :: x.1, x.2) := by
        funext x
        rcases x with ⟨a, g, b⟩
        simp [whL]
      rw [hm]
    _ = _ := hstep

private theorem wt_up_after_down (j : I) (μ : X) :
    wt D (wt D μ [dn j]) [up j] = μ := by simp [wt, sh]

private theorem bubbleMate_right (j : I) (μ : X) {p : ZMod 2}
    {b : (pres D Sc).obj (ob D (wt D μ [dn j]) []) ⟶ (pres D Sc).obj (ob D (wt D μ [dn j]) [])}
    (hb : b ∈ closedPar D Sc (wt D μ [dn j]) p) :
    bubbleMate (Sc := Sc) j μ (rbub j (wt D μ [dn j]) b) = plcL D Sc μ [] [dn j] [] [] b := by
  induction hb using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, _, rfl⟩ := hf
    unfold rbub
    erw [plcL_cl, bubbleMate_cl, plcL_cl]
    exact mate_closed_right j μ hL
  | zero => unfold rbub; erw [map_zero, map_zero, map_zero]
  | add x y _ _ hx hy =>
    unfold rbub at *
    erw [map_add, map_add, map_add, hx, hy]
  | smul a x _ hx =>
    unfold rbub at *
    erw [map_smul, map_smul, map_smul, hx]

private theorem bubbleMate_left (j : I) (μ : X) {p : ZMod 2}
    {b : (pres D Sc).obj (ob D (wt D (wt D μ [dn j]) [up j]) []) ⟶
      (pres D Sc).obj (ob D (wt D (wt D μ [dn j]) [up j]) [])}
    (hb : b ∈ closedPar D Sc (wt D (wt D μ [dn j]) [up j]) p) :
    bubbleMate (Sc := Sc) j μ (lbub j (wt D μ [dn j]) b) =
      plcL D Sc μ [dn j] [] [] [] (regionCast (wt_up_after_down j μ) b) := by
  induction hb using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, _, rfl⟩ := hf
    unfold lbub
    erw [plcL_cl, bubbleMate_cl, regionCast_cl, plcL_cl]
    exact mate_closed_left j μ hL
  | zero => unfold lbub; erw [map_zero, map_zero, regionCast_zero, map_zero]
  | add x y _ _ hx hy =>
    unfold lbub at *
    erw [map_add, map_add, regionCast_add, map_add, hx, hy]
  | smul a x _ hx =>
    unfold lbub at *
    erw [map_smul, map_smul, regionCast_smul, map_smul, hx]

/-- Corollary 7.4, downward generator, by the even right-adjunction mate. -/
theorem oddBubble_slide_down (i j : I) (μ : X) (hi : D.parity i = 1) :
    plcL D Sc μ [] [dn j] [] [] (oddBubble cs i (wt D μ [dn j])) =
      plcL D Sc μ [dn j] [] [] [] (oddBubble cs i (wt D μ [])) := by
  have H := congrArg (bubbleMate (Sc := Sc) j μ) (oddBubble_slide_up cs i j (wt D μ [dn j]) hi)
  erw [bubbleMate_right j μ (oddBubble_mem cs i _), bubbleMate_left j μ (oddBubble_mem cs i _),
    regionCast_family] at H
  exact H

/-- Odd-bubble action on an arbitrary word, on its leftmost region. -/
def oddBubbleAction (i : I) (μ : X) (s : List (Letter I)) :
    (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ s) :=
  plcL D Sc μ [] s [] [] (oddBubble cs i (wt D μ s))

private theorem plcRight_nil_of_mem (μ : X) {s t : List (Letter I)} {q : ZMod 2}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ homPar D Sc μ s t q) : plcRight μ [] s t f = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, _, _, rfl⟩ := hf
    rw [plcRight_cl, map_whL_nil_nil]
    rfl
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

/-- The actual odd-bubble actions are supernatural for every homogeneous
2-morphism between arbitrary boundary words. The sign is its full parity,
not an even-morphism restriction. -/
theorem oddBubble_naturality (i : I) (μ : X) (hi : D.parity i = 1)
    {s t : List (Letter I)} (hw : wt D μ s = wt D μ t) {q : ZMod 2}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ homPar D Sc μ s t q) :
    oddBubbleAction cs i μ s ≫ f = zsign k q • (f ≫ oddBubbleAction cs i μ t) := by
  have H := plcL_interchange_hom μ hw (oddBubble_mem cs i (wt D μ s)) hf
  erw [plcRight_nil_of_mem μ hf, regionCast_family, hi, one_mul] at H
  exact H

/-- An inhomogeneous 2-morphism is handled by linearity, with the odd part
changing sign. No summand is assumed even. -/
theorem oddBubble_naturality_add (i : I) (μ : X) (hi : D.parity i = 1)
    {s t : List (Letter I)} (hw : wt D μ s = wt D μ t)
    {f₀ f₁ : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (h₀ : f₀ ∈ homPar D Sc μ s t 0) (h₁ : f₁ ∈ homPar D Sc μ s t 1) :
    oddBubbleAction cs i μ s ≫ (f₀ + f₁) = (f₀ - f₁) ≫ oddBubbleAction cs i μ t := by
  rw [Preadditive.comp_add, oddBubble_naturality cs i μ hi hw h₀,
    oddBubble_naturality cs i μ hi hw h₁, zsign_zero, zsign_one', one_smul, neg_one_smul,
    ← sub_eq_add_neg, Preadditive.sub_comp]

end OddMath.SKM
