/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleSlideMiddle
/-!
# Dotted middle-weight braid contractions

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
proof of Proposition 7.3(iii): the rotated braid relation (3.8), with an
arbitrary number of dots, is contracted with the original left cup and cap.
The surviving curl is evaluated by (3.3), (2.14), and the cup pitchfork (7.5).
All colour parities and rectangular polynomial correction coefficients are retained.

The recurrence is an input to, not an assertion of, the all-degree slide identities.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- Evaluation of the actual dotted sideways crossing followed by the left cap. -/
theorem sigma_dots_epsP_expansion (i : I) (μ : X) (n : ℕ) :
    cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i ++ dotsL [dn i] i [] n) ≫
      epsP cs i μ =
    zsign k (D.parity i * D.parity i * n) •
      (cl D Sc μ [up i, dn i] [up i, dn i] (dotsL [] i [dn i] n) ≫
        cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫ epsP cs i μ) +
    ∑ r ∈ range n, zsign k (D.parity i * r) •
      (cl D Sc μ [up i, dn i] [] (epsL i r) ≫ bubR cs i μ (n - 1 - r : ℕ)) := by
  have H := congrArg (fun f => f ≫ epsP cs i μ) (lemma31_eq3_eq Sc i μ n)
  rw [Preadditive.sub_comp, Linear.smul_comp, sub_eq_iff_eq_add] at H
  rw [H]
  erw [← cl_comp (sChain_dL i n) (sChain_sigmaL i i)]
  rw [Preadditive.sum_comp]
  simp only [Linear.smul_comp, Category.assoc, cl_capcup, ← bubR_nat]
  rw [add_comm]

theorem sigma_dots_epsP_expansion_zero (i : I) (μ : X) (n : ℕ)
    (hh : D.h i μ < 0) (hn : (n : ℤ) < -D.h i μ) :
    cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i ++ dotsL [dn i] i [] n) ≫
      epsP cs i μ = 0 := by
  rw [sigma_dots_epsP_expansion, eq_2_14_a cs i μ hh, Limits.comp_zero, smul_zero, zero_add]
  apply sum_eq_zero
  intro r hr
  rw [mem_range] at hr
  rw [bubR_eq_zero_of_lt cs i μ (by omega), Limits.comp_zero, smul_zero]

theorem bubble_slide_term8_dotted (i j : I) (μ : X) (r q s n : ℕ) :
    cupAt cs i μ [up j] [] ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j]
        (term8 i j r q s ++ dotsL [dn i] i [up j] n) ≫ capAt cs i μ [] [up j] =
    bubbleL_right cs i j μ s ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
      bubbleR_left cs i j μ (r + n : ℕ) := by
  have he : term8 i j r q s ++ dotsL [dn i] i [up j] n = term8 i j (r + n) q s := by
    simp only [term8, dotsL, List.replicate_add, List.append_assoc]
  rw [he, bubble_slide_term8]

theorem bubble_slide_braid_lhs_dotted_zero (i j : I) (μ : X) (n : ℕ)
    (hh : 0 < D.h i μ) :
    cupAt cs i μ [up j] [] ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j]
        (lemma33_eq8_lhs i j i ++ dotsL [dn i] i [up j] n) ≫
      capAt cs i μ [] [up j] = 0 := by
  have hs : SChain [up j, up i, dn i] ((sigmaL i i).map (whL [up j] [])) [up j, dn i, up i] := by
    simpa using (sChain_sigmaL i i).whisk [up j] []
  have ht : SChain [up j, dn i, up i] ((sigmaL i j).map (whL [] [up i])) [dn i, up j, up i] := by
    simpa using (sChain_sigmaL i j).whisk [] [up i]
  have hc : SChain [dn i, up j, up i] (crossL [dn i] j i []) [dn i, up i, up j] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hd : SChain [dn i, up i, up j] (dotsL [dn i] i [up j] n) [dn i, up i, up j] :=
    sChain_dotsL [dn i] i [up j] n
  rw [lemma33_eq8_lhs]
  erw [← cl_comp ((hs.append ht).append hc) hd]
  rw [← cl_comp (hs.append ht) hc, ← cl_comp hs ht]
  have hz := congrArg (plcL D Sc μ [up j] [] [] [dn i, up i])
    (eq_2_13_a cs i (wt D μ []) (by simpa using hh))
  rw [map_zero, plcL_comp_of_mem μ [up j] [] (etaP_mem cs i _) (sigma_mem i _), plcL_cl] at hz
  change plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫ _ ≫ _ = _
  simp only [← Category.assoc]
  erw [hz]
  simp

theorem bubble_slide_braid_rhs_dotted_zero (i j : I) (μ : X) (n : ℕ)
    (hn : (n : ℤ) < D.d i j - D.h i μ) :
    cupAt cs i μ [up j] [] ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j]
        (lemma33_eq8_rhs i j i ++ dotsL [dn i] i [up j] n) ≫
      capAt cs i μ [] [up j] = 0 := by
  have hc : SChain [up j, up i, dn i] (crossL [] j i [dn i]) [up i, up j, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have ht : SChain [up i, up j, dn i] ((sigmaL i j).map (whL [up i] [])) [up i, dn i, up j] := by
    simpa using (sChain_sigmaL i j).whisk [up i] []
  have hs : SChain [up i, dn i, up j] ((sigmaL i i).map (whL [] [up j])) [dn i, up i, up j] := by
    simpa using (sChain_sigmaL i i).whisk [] [up j]
  have hd : SChain [dn i, up i, up j] (dotsL [dn i] i [up j] n) [dn i, up i, up j] :=
    sChain_dotsL [dn i] i [up j] n
  have hw : D.h i (wt D μ [up j]) < 0 := by rw [h_wt_upj]; omega
  have hz := congrArg (plcL D Sc μ [] [up j] [up i, dn i] [])
    (sigma_dots_epsP cs i (wt D μ [up j]) hw n (by rw [h_wt_upj]; omega))
  rw [map_zero, plcL_comp_of_mem μ [] [up j]
    (cl_mem_homPar ((sChain_sigmaL i i).append (sChain_dR i n)) rfl) (epsP_mem cs i _), plcL_cl] at hz
  have he : ((sigmaL i i ++ dotsL [dn i] i [] n).map (whL [] [up j])) =
      (sigmaL i i).map (whL [] [up j]) ++ dotsL [dn i] i [up j] n := by
    simp [dotsL, whL]
  rw [he] at hz
  erw [← cl_comp hs hd] at hz
  rw [lemma33_eq8_rhs]
  erw [← cl_comp ((hc.append ht).append hs) hd]
  rw [← cl_comp (hc.append ht) hs, ← cl_comp hc ht]
  change _ ≫ _ ≫ plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) = _
  simp only [Category.assoc] at hz ⊢
  erw [hz]
  simp

/-- The dotted recurrence in the entire missing middle band; `n` is the number of extra dots. -/
theorem bubble_slide_middle_dotted_recurrence (i j : I) (μ : X) (hij : i ≠ j)
    (hpos : 0 < D.h i μ) (n : ℕ) (hn : (n : ℤ) < D.d i j - D.h i μ) :
    (∑ s ∈ range (D.dn i j), (zsign k (D.parity i * s) * (Sc.t i j : k)) •
      (bubbleL_right cs i j μ s ≫ bubbleR_left cs i j μ (D.dn i j - 1 - s + n : ℕ))) +
    (∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i), ∑ s ∈ range p,
      (zsign k (D.parity i * s) * Sc.s i j p q) •
        (bubbleL_right cs i j μ s ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
          bubbleR_left cs i j μ (p - 1 - s + n : ℕ))) = 0 := by
  have hd : SChain [dn i, up i, up j] (dotsL [dn i] i [up j] n) [dn i, up i, up j] :=
    sChain_dotsL [dn i] i [up j] n
  have H := congrArg (fun f => cupAt cs i μ [up j] [] ≫ f ≫
    cl D Sc μ [dn i, up i, up j] [dn i, up i, up j] (dotsL [dn i] i [up j] n) ≫
    capAt cs i μ [] [up j]) (lemma33_eq8_eq Sc i j μ hij)
  simp only [Preadditive.sub_comp, Preadditive.comp_sub,
    Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
    Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul, ← Category.assoc] at H
  have ht (r q s : ℕ) : SChain [up j, up i, dn i] (term8 i j r q s) [dn i, up i, up j] := by
    unfold term8
    rw [List.append_assoc, List.append_assoc, List.append_assoc]
    apply (sChain_dotsL [up j] i [dn i] s).append
    apply SChain.append (t' := [up j]) (by simp [Shape.dom, Shape.cod])
    apply (sChain_dotsL [] j [] q).append
    exact SChain.append (by simp [Shape.dom, Shape.cod]) (sChain_dotsL [dn i] i [up j] r)
  have hl : SChain [up j, up i, dn i] (lemma33_eq8_lhs i j i) [dn i, up i, up j] := by
    simp [lemma33_eq8_lhs, sigmaL, crossL, whL, Shape.dom, Shape.cod]
  have hr : SChain [up j, up i, dn i] (lemma33_eq8_rhs i j i) [dn i, up i, up j] := by
    simp [lemma33_eq8_rhs, sigmaL, crossL, whL, Shape.dom, Shape.cod]
  have happend (L : List (LayerData I)) (hL : SChain [up j, up i, dn i] L [dn i, up i, up j]) :
      cupAt cs i μ [up j] [] ≫ cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] L ≫
        cl D Sc μ [dn i, up i, up j] [dn i, up i, up j] (dotsL [dn i] i [up j] n) ≫
        capAt cs i μ [] [up j] =
      cupAt cs i μ [up j] [] ≫ cl D Sc μ [up j, up i, dn i] [dn i, up i, up j]
        (L ++ dotsL [dn i] i [up j] n) ≫ capAt cs i μ [] [up j] := by
    erw [← cl_comp hL hd]
    simp only [Category.assoc]
  simp only [Category.assoc, happend _ hl, happend _ hr, happend _ (ht _ _ _)] at H
  simp only [bubble_slide_braid_lhs_dotted_zero cs i j μ n hpos,
    bubble_slide_braid_rhs_dotted_zero cs i j μ n hn, sub_self,
    bubble_slide_term8_dotted] at H
  simp only [dotsL, List.replicate_zero, cl_nil, Category.id_comp] at H
  exact H.symm

/-- For negative weight, the entire dotted curl is a signed bubble sum, at every dot count. -/
theorem sigma_dots_epsP_neg (i : I) (μ : X) (hh : D.h i μ < 0) (n : ℕ) :
    cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i ++ dotsL [dn i] i [] n) ≫
      epsP cs i μ =
    ∑ r ∈ range n, zsign k (D.parity i * r) •
      (cl D Sc μ [up i, dn i] [] (epsL i r) ≫ bubR cs i μ (n - 1 - r : ℕ)) := by
  rw [sigma_dots_epsP_expansion, eq_2_14_a cs i μ hh, Limits.comp_zero, smul_zero, zero_add]

/-- The dotted right braid contraction, with its curl fully evaluated in the original maps. -/
theorem bubble_slide_braid_rhs_dotted (i j : I) (μ : X) (hij : i ≠ j)
    (hlt : D.h i μ < D.d i j) (n : ℕ) :
    cupAt cs i μ [up j] [] ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j]
        (lemma33_eq8_rhs i j i ++ dotsL [dn i] i [up j] n) ≫
      capAt cs i μ [] [up j] =
    ∑ r ∈ range n, zsign k (D.parity i * r) •
      (bubbleL_left cs i j μ r ≫ bubbleR_left cs i j μ (n - 1 - r : ℕ)) := by
  have hc : SChain [up j, up i, dn i] (crossL [] j i [dn i]) [up i, up j, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have ht : SChain [up i, up j, dn i] ((sigmaL i j).map (whL [up i] [])) [up i, dn i, up j] := by
    simpa using (sChain_sigmaL i j).whisk [up i] []
  have hs : SChain [up i, dn i, up j] ((sigmaL i i).map (whL [] [up j])) [dn i, up i, up j] := by
    simpa using (sChain_sigmaL i i).whisk [] [up j]
  have hd : SChain [dn i, up i, up j] (dotsL [dn i] i [up j] n) [dn i, up i, up j] :=
    sChain_dotsL [dn i] i [up j] n
  rw [lemma33_eq8_rhs]
  erw [← cl_comp ((hc.append ht).append hs) hd]
  rw [← cl_comp (hc.append ht) hs, ← cl_comp hc ht]
  simp only [← Category.assoc]
  change (((pcuL cs i j μ ≫ pcuS i j μ) ≫ _) ≫ _) ≫ _ = _
  have hp : pcuL cs i j μ ≫ pcuS i j μ = cupAt cs i μ [] [up j] := by
    rw [eq_7_5_b, pcuR, Category.assoc, pcuT_S i j μ hij]
    erw [Category.comp_id]
  rw [hp]
  simp only [Category.assoc]
  have hw : D.h i (wt D μ [up j]) < 0 := by rw [h_wt_upj]; omega
  have H := congrArg (plcL D Sc μ [] [up j] [up i, dn i] [])
    (sigma_dots_epsP_neg cs i (wt D μ [up j]) hw n)
  rw [plcL_comp_of_mem μ [] [up j]
    (cl_mem_homPar ((sChain_sigmaL i i).append (sChain_dR i n)) rfl) (epsP_mem cs i _), plcL_cl] at H
  simp only [map_sum, map_smul] at H
  have he : ((sigmaL i i ++ dotsL [dn i] i [] n).map (whL [] [up j])) =
      (sigmaL i i).map (whL [] [up j]) ++ dotsL [dn i] i [up j] n := by
    simp [dotsL, whL]
  rw [he] at H
  erw [← cl_comp hs hd] at H
  simp only [Category.assoc] at H
  change _ ≫ _ ≫ _ ≫ plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) = _
  erw [H]
  rw [Preadditive.comp_sum]
  apply sum_congr rfl
  intro r _
  rw [Linear.comp_smul]
  congr 1
  rw [plcL_comp_of_mem μ [] [up j] (cl_mem_homPar (sChain_epsL i r) rfl)
    (bubR_mem cs i _ _), ← Category.assoc]
  change (plcL D Sc μ [] [up j] [] [up i, dn i] (etaP cs i (wt D μ [up j])) ≫ _) ≫ _ = _
  rw [← plcL_comp_of_mem μ [] [up j] (etaP_mem cs i _) (cl_mem_homPar (sChain_epsL i r) rfl),
    ← bubL_nat]
  rfl

theorem bubble_slide_middle_dotted_all (i j : I) (μ : X) (hij : i ≠ j)
    (hpos : 0 < D.h i μ) (hlt : D.h i μ < D.d i j) (n : ℕ) :
    (∑ s ∈ range (D.dn i j), (zsign k (D.parity i * s) * (Sc.t i j : k)) •
      (bubbleL_right cs i j μ s ≫ bubbleR_left cs i j μ (D.dn i j - 1 - s + n : ℕ))) +
    (∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i), ∑ s ∈ range p,
      (zsign k (D.parity i * s) * Sc.s i j p q) •
        (bubbleL_right cs i j μ s ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
          bubbleR_left cs i j μ (p - 1 - s + n : ℕ))) =
    -(∑ r ∈ range n, zsign k (D.parity i * r) •
      (bubbleL_left cs i j μ r ≫ bubbleR_left cs i j μ (n - 1 - r : ℕ))) := by
  have hd : SChain [dn i, up i, up j] (dotsL [dn i] i [up j] n) [dn i, up i, up j] :=
    sChain_dotsL [dn i] i [up j] n
  have H := congrArg (fun f => cupAt cs i μ [up j] [] ≫ f ≫
    cl D Sc μ [dn i, up i, up j] [dn i, up i, up j] (dotsL [dn i] i [up j] n) ≫
    capAt cs i μ [] [up j]) (lemma33_eq8_eq Sc i j μ hij)
  simp only [Preadditive.sub_comp, Preadditive.comp_sub,
    Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
    Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul, ← Category.assoc] at H
  have ht (r q s : ℕ) : SChain [up j, up i, dn i] (term8 i j r q s) [dn i, up i, up j] := by
    unfold term8
    rw [List.append_assoc, List.append_assoc, List.append_assoc]
    apply (sChain_dotsL [up j] i [dn i] s).append
    apply SChain.append (t' := [up j]) (by simp [Shape.dom, Shape.cod])
    apply (sChain_dotsL [] j [] q).append
    exact SChain.append (by simp [Shape.dom, Shape.cod]) (sChain_dotsL [dn i] i [up j] r)
  have hl : SChain [up j, up i, dn i] (lemma33_eq8_lhs i j i) [dn i, up i, up j] := by
    simp [lemma33_eq8_lhs, sigmaL, crossL, whL, Shape.dom, Shape.cod]
  have hr : SChain [up j, up i, dn i] (lemma33_eq8_rhs i j i) [dn i, up i, up j] := by
    simp [lemma33_eq8_rhs, sigmaL, crossL, whL, Shape.dom, Shape.cod]
  have happend (L : List (LayerData I)) (hL : SChain [up j, up i, dn i] L [dn i, up i, up j]) :
      cupAt cs i μ [up j] [] ≫ cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] L ≫
        cl D Sc μ [dn i, up i, up j] [dn i, up i, up j] (dotsL [dn i] i [up j] n) ≫
        capAt cs i μ [] [up j] =
      cupAt cs i μ [up j] [] ≫ cl D Sc μ [up j, up i, dn i] [dn i, up i, up j]
        (L ++ dotsL [dn i] i [up j] n) ≫ capAt cs i μ [] [up j] := by
    erw [← cl_comp hL hd]
    simp only [Category.assoc]
  simp only [Category.assoc, happend _ hl, happend _ hr, happend _ (ht _ _ _)] at H
  simp only [bubble_slide_braid_lhs_dotted_zero cs i j μ n hpos,
    bubble_slide_braid_rhs_dotted cs i j μ hij hlt n, zero_sub, bubble_slide_term8_dotted] at H
  simp only [dotsL, List.replicate_zero, cl_nil, Category.id_comp] at H
  exact H.symm

end OddMath.SKM
