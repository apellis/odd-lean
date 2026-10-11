/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleSlidePolynomial
import OddMath.SKM.Lemma33Rot
/-!
# The initial connected middle-weight bubble recurrence

Contracting Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Lemma 3.3, (3.8), with the left cup and cap gives the undotted (shifted degree one)
case of the recurrence used in the proof of Proposition 7.3(iii).
For `0 < hᵢ(μ) < dᵢⱼ`, both braid composites vanish by the defining inversion
relations (2.13)–(2.14). The full polynomial correction survives, in the order
`counterclockwise bubble; strand dots; clockwise bubble`. No commutation is used.

This initial recurrence does not assert the higher dotted recurrences or the
all-degree fake-bubble slides.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

theorem bubble_slide_term8 (i j : I) (μ : X) (r q s : ℕ) :
    cupAt cs i μ [up j] [] ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (term8 i j r q s) ≫
      capAt cs i μ [] [up j] =
    bubbleL_right cs i j μ s ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
      bubbleR_left cs i j μ r := by
  have he : SChain [up j, up i, dn i] ((epsL i s).map (whL [up j] [])) [up j] := by
    simpa using (sChain_epsL i s).whisk [up j] []
  have hd : SChain [up j] (dotsL [] j [] q) [up j] := sChain_dotsL [] j [] q
  have hc : SChain [up j] ((etaL i r).map (whL [] [up j])) [dn i, up i, up j] := by
    simpa using (sChain_etaL i r).whisk [] [up j]
  have ht : term8 i j r q s =
      (epsL i s).map (whL [up j] []) ++ dotsL [] j [] q ++ (etaL i r).map (whL [] [up j]) := by
    simp [term8, epsL, etaL, dotsL, whL, List.map_replicate, List.append_assoc]
  rw [ht, ← cl_comp (he.append hd) hc, ← cl_comp he hd]
  change plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫ _ ≫
    plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) = _
  have hl : bubbleL_right cs i j μ s =
      plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
        cl D Sc μ [up j, up i, dn i] [up j] ((epsL i s).map (whL [up j] [])) := by
    change plcL D Sc μ [up j] [] [] [] (bubL cs i (wt D μ []) s) = _
    rw [bubL_nat, plcL_comp_of_mem μ [up j] [] (etaP_mem cs i _)
      (cl_mem_homPar (sChain_epsL i s) rfl), plcL_cl]
    rfl
  have hr : bubbleR_left cs i j μ r =
      cl D Sc μ [up j] [dn i, up i, up j] ((etaL i r).map (whL [] [up j])) ≫
        plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) := by
    change plcL D Sc μ [] [up j] [] [] (bubR cs i (wt D μ [up j]) r) = _
    rw [bubR_nat, plcL_comp_of_mem μ [] [up j] (cl_mem_homPar (sChain_etaL i r) rfl)
      (epsP_mem cs i _), plcL_cl]
    rfl
  rw [hl, hr]
  simp only [Category.assoc]

theorem bubble_slide_braid_lhs_zero (i j : I) (μ : X) (hh : 0 < D.h i μ) :
    cupAt cs i μ [up j] [] ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (lemma33_eq8_lhs i j i) ≫
      capAt cs i μ [] [up j] = 0 := by
  have hs : SChain [up j, up i, dn i] ((sigmaL i i).map (whL [up j] [])) [up j, dn i, up i] := by
    simpa using (sChain_sigmaL i i).whisk [up j] []
  have ht : SChain [up j, dn i, up i] ((sigmaL i j).map (whL [] [up i])) [dn i, up j, up i] := by
    simpa using (sChain_sigmaL i j).whisk [] [up i]
  have hc : SChain [dn i, up j, up i] (crossL [dn i] j i []) [dn i, up i, up j] := by
    simp [crossL, Shape.dom, Shape.cod]
  rw [lemma33_eq8_lhs, ← cl_comp (hs.append ht) hc, ← cl_comp hs ht]
  have hz := congrArg (plcL D Sc μ [up j] [] [] [dn i, up i])
    (eq_2_13_a cs i (wt D μ []) (by simpa using hh))
  rw [map_zero, plcL_comp_of_mem μ [up j] [] (etaP_mem cs i _) (sigma_mem i _), plcL_cl] at hz
  change plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫ _ ≫ _ = _
  simp only [← Category.assoc]
  erw [hz]
  simp

theorem bubble_slide_braid_rhs_zero (i j : I) (μ : X) (hh : D.h i μ < D.d i j) :
    cupAt cs i μ [up j] [] ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (lemma33_eq8_rhs i j i) ≫
      capAt cs i μ [] [up j] = 0 := by
  have hc : SChain [up j, up i, dn i] (crossL [] j i [dn i]) [up i, up j, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have ht : SChain [up i, up j, dn i] ((sigmaL i j).map (whL [up i] [])) [up i, dn i, up j] := by
    simpa using (sChain_sigmaL i j).whisk [up i] []
  have hs : SChain [up i, dn i, up j] ((sigmaL i i).map (whL [] [up j])) [dn i, up i, up j] := by
    simpa using (sChain_sigmaL i i).whisk [] [up j]
  rw [lemma33_eq8_rhs, ← cl_comp (hc.append ht) hs, ← cl_comp hc ht]
  have hw : D.h i (wt D μ [up j]) < 0 := by
    rw [h_wt_upj]
    omega
  have hz := congrArg (plcL D Sc μ [] [up j] [up i, dn i] []) (eq_2_14_a cs i (wt D μ [up j]) hw)
  rw [map_zero, plcL_comp_of_mem μ [] [up j] (sigma_mem i _) (epsP_mem cs i _), plcL_cl] at hz
  change _ ≫ _ ≫ plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) = _
  simp only [Category.assoc]
  erw [hz]
  simp

/-- The first middle-weight recurrence, from the contracted rotated braid relation. -/
theorem bubble_slide_middle_recurrence (i j : I) (μ : X) (hij : i ≠ j)
    (hpos : 0 < D.h i μ) (hlt : D.h i μ < D.d i j) :
    (∑ s ∈ range (D.dn i j), (zsign k (D.parity i * s) * (Sc.t i j : k)) •
      (bubbleL_right cs i j μ s ≫ bubbleR_left cs i j μ (D.dn i j - 1 - s : ℕ))) +
    (∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i), ∑ s ∈ range p,
      (zsign k (D.parity i * s) * Sc.s i j p q) •
        (bubbleL_right cs i j μ s ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
          bubbleR_left cs i j μ (p - 1 - s : ℕ))) = 0 := by
  have H := congrArg (fun f => cupAt cs i μ [up j] [] ≫ f ≫ capAt cs i μ [] [up j])
    (lemma33_eq8_eq Sc i j μ hij)
  simp only [Preadditive.sub_comp, Preadditive.comp_sub,
    bubble_slide_braid_lhs_zero cs i j μ hpos, bubble_slide_braid_rhs_zero cs i j μ hlt,
    sub_self, Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
    Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul, bubble_slide_term8,
    dotsL, List.replicate_zero, cl_nil, Category.id_comp] at H
  exact H.symm
end OddMath.SKM
