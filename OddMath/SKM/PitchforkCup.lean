/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PitchforkCap
/-!
# The all-weight cup pitchfork

The second equality in Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 7.2, (7.5). It follows from the all-weight
cap equality by opening both outer legs and applying the left adjunctions.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- Opening the two outer downward legs of a cap pitchfork. -/
def bendCap (i j : I) (μ : X)
    (f : (pres D Sc).obj (ob D (wt D μ [dn i]) [dn i, up j, up i]) ⟶
      (pres D Sc).obj (ob D (wt D μ [dn i]) [up j])) :
    (pres D Sc).obj (ob D μ [up j]) ⟶ (pres D Sc).obj (ob D μ [up i, up j, dn i]) :=
  cupAt cs i μ [up j] [] ≫ cupAt cs i μ [] [up j, up i, dn i] ≫
    plcL D Sc μ [up i] [dn i] [dn i, up j, up i] [up j] f

theorem nested_cap_L (i j : I) (μ : X) :
    plcL D Sc μ [up i] [dn i] [dn i, up i, up j] [up j]
      (capAt cs i (wt D μ [dn i]) [] [up j]) =
    capAt cs i μ [up i] [up j, dn i] := by
  have E := plcL_nested μ [up i] [dn i] [] [up j]
    (epsP_mem cs i (wt D (wt D μ [dn i]) [up j]))
  simpa only [capAt, regionCast_family, List.cons_append, List.nil_append, wordCast, LinearMap.id_apply] using E

theorem nested_cap_R (i j : I) (μ : X) :
    plcL D Sc μ [up i] [dn i] [up j, dn i, up i] [up j]
      (capAt cs i (wt D μ [dn i]) [up j] []) =
    capAt cs i μ [up i, up j] [dn i] := by
  have E := plcL_nested μ [up i] [dn i] [up j] []
    (epsP_mem cs i (wt D (wt D μ [dn i]) []))
  simpa only [capAt, regionCast_family, List.cons_append, List.nil_append, wordCast, LinearMap.id_apply] using E

theorem bendCap_L_expand (i j : I) (μ : X) :
    bendCap cs i j μ (pfL cs i j (wt D μ [dn i])) =
      cupAt cs i μ [up j] [] ≫ cupAt cs i μ [] [up j, up i, dn i] ≫
        cl D Sc μ [up i, dn i, up j, up i, dn i] [up i, dn i, up i, up j, dn i]
          (crossL [up i, dn i] j i [dn i]) ≫ capAt cs i μ [up i] [up j, dn i] := by
  have hc : capAt cs i (wt D μ [dn i]) [] [up j] ∈
      homPar D Sc (wt D μ [dn i]) [dn i, up i, up j] [up j] _ :=
    plcL_mem _ [] [up j] (epsP_mem cs i _)
  have hl : SChain [dn i, up j, up i] (crossL [dn i] j i []) [dn i, up i, up j] := by
    simp [crossL, Shape.dom, Shape.cod]
  rw [bendCap, pfL, plcL_comp_of_mem μ [up i] [dn i] (cl_mem_homPar hl rfl) hc]
  rw [nested_cap_L, plcL_cl]
  rfl

theorem bendCap_R_expand (i j : I) (μ : X) :
    bendCap cs i j μ (pfR cs i j (wt D μ [dn i])) =
      cupAt cs i μ [up j] [] ≫ cupAt cs i μ [] [up j, up i, dn i] ≫
        cl D Sc μ [up i, dn i, up j, up i, dn i] [up i, up j, dn i, up i, dn i]
          ((lcrossL i j).map (whL [up i] [up i, dn i])) ≫ capAt cs i μ [up i, up j] [dn i] := by
  have hc : capAt cs i (wt D μ [dn i]) [up j] [] ∈
      homPar D Sc (wt D μ [dn i]) [up j, dn i, up i] [up j] _ :=
    plcL_mem _ [up j] [] (epsP_mem cs i _)
  have hl : SChain [dn i, up j, up i] ((lcrossL i j).map (whL [] [up i])) [up j, dn i, up i] := by
    simpa using (sChain_lcrossL i j).whisk [] [up i]
  rw [bendCap, pfR]
  erw [plcL_comp_of_mem μ [up i] [dn i] (cl_mem_homPar hl rfl) hc]
  rw [nested_cap_R, plcL_cl]
  rfl

theorem cup_cap_E_ctx' (i j : I) (μ : X) :
    cupAt cs i μ [] [up i, up j, dn i] ≫ capAt cs i μ [up i] [up j, dn i] =
      zsign k (ipar D i (wt D μ [up j, dn i])) • 𝟙 _ := by
  have E := congrArg (plcL D Sc μ [] [up j, dn i] [up i] [up i])
    (eq_6_6_a cs i (wt D μ [up j, dn i]))
  have hc : leta cs i (wt D μ [up j, dn i]) ∈
      homPar D Sc (wt D μ [up j, dn i]) [up i] [up i, dn i, up i] _ :=
    plcL_mem _ [] [up i] (etaP_mem cs i _)
  have he : reps cs i (wt D μ [up j, dn i]) ∈
      homPar D Sc (wt D μ [up j, dn i]) [up i, dn i, up i] [up i] _ :=
    plcL_mem _ [up i] [] (epsP_mem cs i _)
  rw [plcL_comp_of_mem μ [] [up j, dn i] hc he, map_smul, plcL_id] at E
  unfold leta reps at E
  have hη := plcL_nested μ [] [up j, dn i] [] [up i]
    (etaP_mem cs i (wt D (wt D μ [up j, dn i]) [up i]))
  have hε := plcL_nested μ [] [up j, dn i] [up i] []
    (epsP_mem cs i (wt D (wt D μ [up j, dn i]) []))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast, LinearMap.id_apply] at hη hε
  erw [hη, hε] at E
  exact E

theorem cup_cap_F_ctx' (i j : I) (μ : X) :
    cupAt cs i μ [up i, up j, dn i] [] ≫ capAt cs i μ [up i, up j] [dn i] = 𝟙 _ := by
  have E := congrArg (plcL D Sc μ [up i, up j] [] [dn i] [dn i]) (eq_6_6_b cs i μ)
  have hc : retaF cs i μ ∈ homPar D Sc μ [dn i] [dn i, up i, dn i] _ :=
    plcL_mem _ [dn i] [] (etaP_mem cs i _)
  have he : lepsF cs i μ ∈ homPar D Sc μ [dn i, up i, dn i] [dn i] _ :=
    plcL_mem _ [] [dn i] (epsP_mem cs i _)
  erw [plcL_comp_of_mem μ [up i, up j] [] hc he, plcL_id] at E
  unfold retaF lepsF at E
  have hη := plcL_nested μ [up i, up j] [] [dn i] []
    (etaP_mem cs i (wt D (wt D μ []) []))
  have hε := plcL_nested μ [up i, up j] [] [] [dn i]
    (epsP_mem cs i (wt D (wt D μ []) [dn i]))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast, LinearMap.id_apply] at hη hε
  erw [hη, hε] at E
  exact E

theorem cup_cross_L (i j : I) (μ : X) :
    cupAt cs i μ [] [up j, up i, dn i] ≫
      cl D Sc μ [up i, dn i, up j, up i, dn i] [up i, dn i, up i, up j, dn i]
        (crossL [up i, dn i] j i [dn i]) =
      zsign k (ipar D i (wt D μ [up j, up i, dn i]) * (D.parity j * D.parity i)) •
        (cl D Sc μ [up j, up i, dn i] [up i, up j, dn i] (crossL [] j i [dn i]) ≫
          cupAt cs i μ [] [up i, up j, dn i]) := by
  have hw : wt D μ [up j, up i, dn i] = wt D μ [up i, up j, dn i] := by
    simp [wt, sh, add_comm, add_left_comm, add_assoc]
  have hg : SChain [up j, up i, dn i] (crossL [] j i [dn i]) [up i, up j, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have E := plcL_interchange_hom μ hw (etaP_mem cs i (wt D μ [up j, up i, dn i]))
    (cl_mem_homPar (D := D) (Sc := Sc) hg rfl)
  simp only [plcRight_cl, regionCast_family, parsum, parity_crossL] at E
  exact E

theorem cup_cup_swap (i j : I) (μ : X) :
    cupAt cs i μ [up j] [] ≫ cupAt cs i μ [] [up j, up i, dn i] =
      zsign k (ipar D i (wt D μ [up j]) * ipar D i μ) •
        (cupAt cs i μ [] [up j] ≫ cupAt cs i μ [up i, dn i, up j] []) := by
  have hw : wt D μ [up j] = wt D μ [up j, up i, dn i] := by simp [wt, sh]
  have hg : cupAt cs i μ [up j] [] ∈
      homPar D Sc μ [up j] [up j, up i, dn i] (ipar D i μ) :=
    plcL_mem _ [up j] [] (etaP_mem cs i _)
  have E := plcL_interchange_hom μ hw (etaP_mem cs i (wt D μ [up j])) hg
  have hn := plcL_nested μ [up i, dn i] [] [up j] [] (etaP_mem cs i (wt D (wt D μ []) []))
  have h0 := plcL_nested μ [] [] [up j] [] (etaP_mem cs i (wt D (wt D μ []) []))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast, LinearMap.id_apply] at hn h0
  simp only [regionCast_family, plcRight, LinearMap.comp_apply, wordCast] at E
  erw [h0, hn] at E
  have EE := congrArg (zsign k (ipar D i (wt D μ [up j]) * ipar D i μ) • ·) E
  rw [smul_smul, zsign_mul_self', one_smul] at EE
  exact EE.symm

theorem cup_cross_R (i j : I) (μ : X) :
    cupAt cs i μ [up i, dn i, up j] [] ≫
      cl D Sc μ [up i, dn i, up j, up i, dn i] [up i, up j, dn i, up i, dn i]
        ((lcrossL i j).map (whL [up i] [up i, dn i])) =
      zsign k ((D.parity i * D.parity j) * ipar D i μ) •
        (cl D Sc μ [up i, dn i, up j] [up i, up j, dn i]
            ((lcrossL i j).map (whL [up i] [])) ≫ cupAt cs i μ [up i, up j, dn i] []) := by
  have hw : wt D μ [] = wt D μ [up i, dn i] := by simp [wt, sh]
  have hf : SChain [up i, dn i, up j] ((lcrossL i j).map (whL [up i] [])) [up i, up j, dn i] := by
    simpa using (sChain_lcrossL i j).whisk [up i] []
  have E := plcL_interchange_hom μ hw
    (cl_mem_homPar (D := D) (Sc := Sc) (μ := wt D μ []) hf rfl) (etaP_mem cs i μ)
  simp only [regionCast_cl, plcL_cl, plcRight, LinearMap.comp_apply, wordCast,
    parsum_map_whL, parsum_lcrossL, List.map_map] at E
  have EE := congrArg (zsign k ((D.parity i * D.parity j) * ipar D i μ) • ·) E
  rw [smul_smul, zsign_mul_self', one_smul] at EE
  exact EE.symm

theorem ipar_wt_dnj (i j : I) (μ : X) : ipar D i (wt D μ [dn j]) = ipar D i μ := by
  have E := ipar_wt_upj (D := D) i j (wt D μ [dn j])
  have hw : wt D (wt D μ [dn j]) [up j] = μ := by simp [wt, sh]
  rw [hw] at E
  exact E.symm

theorem bendCap_L (i j : I) (μ : X) :
    bendCap cs i j μ (pfL cs i j (wt D μ [dn i])) =
      zsign k (ipar D i μ * (D.parity i * D.parity j) + ipar D i μ) • pcuL cs i j μ := by
  have hp : ipar D i (wt D μ [up j, up i, dn i]) = ipar D i μ := by
    have hw : wt D μ [up j, up i, dn i] = wt D μ [up j] := by simp [wt, sh]
    rw [hw, ipar_wt_upj]
  have hq : ipar D i (wt D μ [up j, dn i]) = ipar D i μ := by
    change ipar D i (wt D μ ([up j] ++ [dn i])) = _
    rw [wt_append, ipar_wt_upj, ipar_wt_dnj]
  rw [bendCap_L_expand, ← Category.assoc (cupAt cs i μ [] [up j, up i, dn i]), cup_cross_L]
  simp only [Linear.smul_comp, Linear.comp_smul]
  erw [Category.assoc, cup_cap_E_ctx', Linear.comp_smul, Category.comp_id, Linear.comp_smul,
    smul_smul, ← zsign_add, hp, hq, mul_comm (D.parity j) (D.parity i)]
  rfl

theorem bendCap_R (i j : I) (μ : X) :
    bendCap cs i j μ (pfR cs i j (wt D μ [dn i])) =
      zsign k (ipar D i μ * (D.parity i * D.parity j) + ipar D i μ) • pcuR cs i j μ := by
  rw [bendCap_R_expand, ← Category.assoc (cupAt cs i μ [up j] []), cup_cup_swap]
  simp only [Linear.smul_comp]
  rw [Category.assoc, ← Category.assoc (cupAt cs i μ [up i, dn i, up j] []), cup_cross_R]
  simp only [Linear.smul_comp, Linear.comp_smul]
  erw [Category.assoc, cup_cap_F_ctx', Category.comp_id, smul_smul, ← zsign_add, ipar_wt_upj]
  have hp : ipar D i μ * ipar D i μ + (D.parity i * D.parity j) * ipar D i μ =
      ipar D i μ * (D.parity i * D.parity j) + ipar D i μ := by
    rw [zmod2_mul_self]; ring
  rw [hp]
  rfl

/-- The cup half of Proposition 7.2, for every weight and pair of colours. -/
theorem eq_7_5_b (i j : I) (μ : X) : pcuL cs i j μ = pcuR cs i j μ := by
  have E := congrArg (bendCap cs i j μ) (eq_7_5_a cs i j (wt D μ [dn i]))
  rw [bendCap_L, bendCap_R] at E
  have E' := congrArg (zsign k (ipar D i μ * (D.parity i * D.parity j) + ipar D i μ) • ·) E
  simpa only [smul_smul, zsign_mul_self', one_smul] using E'

end OddMath.SKM
