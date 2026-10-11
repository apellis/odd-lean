/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PitchforkCup
/-!
# Disconnected bubble slides with natural dot counts

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 7.3(iv), (7.13)–(7.14), before the shifted-degree extension.
Both slides carry a factor `tᵢⱼ` on the right. These factors are derived from
the defining quadratic relations, not imposed as additional relations.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- A clockwise bubble placed to the left of an upward strand. -/
abbrev bubbleR_left (i j : I) (μ : X) (n : ℤ) := lbub j μ (bubR cs i (wt D μ [up j]) n)
/-- A clockwise bubble placed to the right of an upward strand. -/
abbrev bubbleR_right (i j : I) (μ : X) (n : ℤ) := rbub j μ (bubR cs i (wt D μ []) n)

theorem bubbleR_slide_quad (i j : I) (μ : X) (hij : i ≠ j) (n : ℕ) :
    bubbleR_right cs i j μ n =
      cl D Sc μ [up j] [dn i, up i, up j]
        ((etaL i n).map (whL [] [up j]) ++ crossL [dn i] i j [] ++ crossL [dn i] j i []) ≫
        capAt cs i μ [] [up j] := by
  change plcL D Sc μ [up j] [] [] [] (bubR cs i (wt D μ []) n) = _
  rw [bubR_nat, ← pfR_b cs i j μ hij n, ← eq_7_5_a, pfL_b_reduce cs i j μ hij n]

theorem bubbleR_slide_zero_raw (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 0) (n : ℕ) :
    bubbleR_right cs i j μ n = (Sc.t i j : k) • bubbleR_left cs i j μ n := by
  rw [bubbleR_slide_quad cs i j μ hij n]
  have het : SChain [up j] ((etaL i n).map (whL [] [up j])) [dn i, up i, up j] := by
    simpa using (sChain_etaL i n).whisk [] [up j]
  have hcc : SChain [dn i, up i, up j] (crossL [dn i] i j [] ++ crossL [dn i] j i [])
      [dn i, up i, up j] := by simp [crossL, Shape.dom, Shape.cod]
  have e0 : cl D Sc μ [up j] [dn i, up i, up j]
      ((etaL i n).map (whL [] [up j]) ++ crossL [dn i] i j [] ++ crossL [dn i] j i []) =
      cl D Sc μ [up j] [dn i, up i, up j] ((etaL i n).map (whL [] [up j])) ≫
        cl D Sc μ [dn i, up i, up j] [dn i, up i, up j]
          (crossL [dn i] i j [] ++ crossL [dn i] j i []) := by
    rw [cl_comp het hcc, List.append_assoc]
  rw [e0, Category.assoc]
  have hq := congrArg (plcL D Sc μ [dn i] [] [up i, up j] [up i, up j])
    (cl_quadZero (Sc := Sc) i j (wt D μ []) hij hd)
  rw [map_smul, plcL_cl, plcL_cl, List.map_nil, cl_nil] at hq
  erw [hq]
  rw [Linear.smul_comp, Linear.comp_smul]
  erw [Category.id_comp]
  congr 1
  change _ = plcL D Sc μ [] [up j] [] [] (bubR cs i (wt D μ [up j]) n)
  rw [bubR_nat, plcL_comp_of_mem μ [] [up j] (cl_mem_homPar (sChain_etaL i n) rfl)
    (epsP_mem cs i _), plcL_cl]
  rfl



abbrev bubbleL_left (i j : I) (μ : X) (n : ℤ) := lbub j μ (bubL cs i (wt D μ [up j]) n)
abbrev bubbleL_right (i j : I) (μ : X) (n : ℤ) := rbub j μ (bubL cs i (wt D μ []) n)

theorem bubbleL_slide_zero_raw (i j : I) (μ : X) (hij : i ≠ j) (hd : D.d i j = 0) (n : ℕ) :
    bubbleL_left cs i j μ n = (Sc.t i j : k) • bubbleL_right cs i j μ n := by
  change plcL D Sc μ [] [up j] [] [] (bubL cs i (wt D μ [up j]) n) = _
  rw [bubL_nat, ← pcuR_b cs i j μ hij n, ← eq_7_5_b, pcuL_b_reduce cs i j μ hij n]
  have hcc : SChain [up j, up i, dn i] (crossL [] j i [dn i] ++ crossL [] i j [dn i])
      [up j, up i, dn i] := by simp [crossL, Shape.dom, Shape.cod]
  have he : SChain [up j, up i, dn i] ((epsL i n).map (whL [up j] [])) [up j] := by
    simpa using (sChain_epsL i n).whisk [up j] []
  rw [← cl_comp hcc he]
  have hq := congrArg (plcL D Sc μ [] [dn i] [up j, up i] [up j, up i])
    (cl_quadZero (Sc := Sc) j i (wt D μ [dn i]) hij.symm ((D.d_eq_zero_iff j i).mpr hd))
  rw [map_smul, plcL_cl, plcL_cl, List.map_nil, cl_nil] at hq
  erw [hq]
  rw [Linear.smul_comp, Linear.comp_smul]
  erw [Category.id_comp]
  rw [← Sc.t_symm_of_d_eq_zero i j hd]
  congr 1
  change _ = plcL D Sc μ [up j] [] [] [] (bubL cs i (wt D μ []) n)
  rw [bubL_nat, plcL_comp_of_mem μ [up j] [] (etaP_mem cs i _)
    (cl_mem_homPar (sChain_epsL i n) rfl), plcL_cl]
  rfl

end OddMath.SKM
