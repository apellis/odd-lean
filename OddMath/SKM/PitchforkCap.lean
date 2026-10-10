/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Lemma71Cup
import OddMath.SKM.PlacementHom
/-!
# The all-weight cap pitchfork

The first equality in Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 7.2, (7.5).

`eq_7_5_a` has no weight or colour restriction. The complementary range is
obtained by closing both outer legs of the cup relation at the shifted weight.
The two bending computations have the same sign, which cancels.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

abbrev cupAt (i : I) (μ : X) (u v : List (Letter I)) :=
  plcL D Sc μ u v [] [up i, dn i] (etaP cs i (wt D μ v))
abbrev capAt (i : I) (μ : X) (u v : List (Letter I)) :=
  plcL D Sc μ u v [dn i, up i] [] (epsP cs i (wt D μ v))

/-- Closing the two outer upward legs of a cup pitchfork. -/
def bendCup (i j : I) (μ : X)
    (f : (pres D Sc).obj (ob D (wt D μ [up i]) [up j]) ⟶
      (pres D Sc).obj (ob D (wt D μ [up i]) [up i, up j, dn i])) :
    (pres D Sc).obj (ob D μ [dn i, up j, up i]) ⟶ (pres D Sc).obj (ob D μ [up j]) :=
  plcL D Sc μ [dn i] [up i] [up j] [up i, up j, dn i] f ≫
    capAt cs i μ [] [up j, dn i, up i] ≫ capAt cs i μ [up j] []

theorem nested_cup_R (i j : I) (μ : X) :
    plcL D Sc μ [dn i] [up i] [up j] [up i, dn i, up j]
      (cupAt cs i (wt D μ [up i]) [] [up j]) =
    cupAt cs i μ [dn i] [up j, up i] := by
  have E := plcL_nested μ [dn i] [up i] [] [up j]
    (etaP_mem cs i (wt D (wt D μ [up i]) [up j]))
  simpa only [cupAt, regionCast_family, List.cons_append, List.nil_append, wordCast, LinearMap.id_apply] using E

theorem nested_cup_L (i j : I) (μ : X) :
    plcL D Sc μ [dn i] [up i] [up j] [up j, up i, dn i]
      (cupAt cs i (wt D μ [up i]) [up j] []) =
    cupAt cs i μ [dn i, up j] [up i] := by
  have E := plcL_nested μ [dn i] [up i] [up j] []
    (etaP_mem cs i (wt D (wt D μ [up i]) []))
  simpa only [cupAt, regionCast_family, List.cons_append, List.nil_append, wordCast, LinearMap.id_apply] using E

theorem bendCup_R_expand (i j : I) (μ : X) :
    bendCup cs i j μ (pcuR cs i j (wt D μ [up i])) =
      cupAt cs i μ [dn i] [up j, up i] ≫
        cl D Sc μ [dn i, up i, dn i, up j, up i] [dn i, up i, up j, dn i, up i]
          ((lcrossL i j).map (whL [dn i, up i] [up i])) ≫
        capAt cs i μ [] [up j, dn i, up i] ≫ capAt cs i μ [up j] [] := by
  have hc : cupAt cs i (wt D μ [up i]) [] [up j] ∈
      homPar D Sc (wt D μ [up i]) [up j] [up i, dn i, up j] _ :=
    plcL_mem _ [] [up j] (etaP_mem cs i _)
  have hl : SChain [up i, dn i, up j] ((lcrossL i j).map (whL [up i] [])) [up i, up j, dn i] := by
    simpa using (sChain_lcrossL i j).whisk [up i] []
  rw [bendCup, pcuR, plcL_comp_of_mem μ [dn i] [up i] hc (cl_mem_homPar hl rfl)]
  rw [nested_cup_R, plcL_cl]
  simp only [List.map_map, Category.assoc]
  rfl

theorem bendCup_L_expand (i j : I) (μ : X) :
    bendCup cs i j μ (pcuL cs i j (wt D μ [up i])) =
      cupAt cs i μ [dn i, up j] [up i] ≫
        cl D Sc μ [dn i, up j, up i, dn i, up i] [dn i, up i, up j, dn i, up i]
          (crossL [dn i] j i [dn i, up i]) ≫
        capAt cs i μ [] [up j, dn i, up i] ≫ capAt cs i μ [up j] [] := by
  have hc : cupAt cs i (wt D μ [up i]) [up j] [] ∈
      homPar D Sc (wt D μ [up i]) [up j] [up j, up i, dn i] _ :=
    plcL_mem _ [up j] [] (etaP_mem cs i _)
  have hl : SChain [up j, up i, dn i] (crossL [] j i [dn i]) [up i, up j, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  rw [bendCup, pcuL, plcL_comp_of_mem μ [dn i] [up i] hc (cl_mem_homPar hl rfl)]
  rw [nested_cup_L, plcL_cl]
  simp only [Category.assoc]
  rfl

theorem cup_cap_F_ctx (i j : I) (μ : X) :
    cupAt cs i μ [dn i] [up j, up i] ≫ capAt cs i μ [] [dn i, up j, up i] = 𝟙 _ := by
  have E := congrArg (plcL D Sc μ [] [up j, up i] [dn i] [dn i])
    (eq_6_6_b cs i (wt D μ [up j, up i]))
  have hc : retaF cs i (wt D μ [up j, up i]) ∈
      homPar D Sc (wt D μ [up j, up i]) [dn i] [dn i, up i, dn i] _ :=
    plcL_mem _ [dn i] [] (etaP_mem cs i _)
  have he : lepsF cs i (wt D μ [up j, up i]) ∈
      homPar D Sc (wt D μ [up j, up i]) [dn i, up i, dn i] [dn i] _ :=
    plcL_mem _ [] [dn i] (epsP_mem cs i _)
  rw [plcL_comp_of_mem μ [] [up j, up i] hc he, plcL_id] at E
  unfold retaF lepsF at E
  have hη := plcL_nested μ [] [up j, up i] [dn i] []
    (etaP_mem cs i (wt D (wt D μ [up j, up i]) []))
  have hε := plcL_nested μ [] [up j, up i] [] [dn i]
    (epsP_mem cs i (wt D (wt D μ [up j, up i]) [dn i]))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast, LinearMap.id_apply] at hη hε
  change _ ≫ _ = _ at E
  erw [hη, hε] at E
  exact E

theorem cross_cap_R (i j : I) (μ : X) :
    cl D Sc μ [dn i, up i, dn i, up j, up i] [dn i, up i, up j, dn i, up i]
        ((lcrossL i j).map (whL [dn i, up i] [up i])) ≫
      capAt cs i μ [] [up j, dn i, up i] =
      zsign k (ipar D i (wt D μ [dn i, up j, up i]) * (D.parity i * D.parity j)) •
        (capAt cs i μ [] [dn i, up j, up i] ≫
          cl D Sc μ [dn i, up j, up i] [up j, dn i, up i]
            ((lcrossL i j).map (whL [] [up i]))) := by
  have hw : wt D μ [dn i, up j, up i] = wt D μ [up j, dn i, up i] := by
    simp [wt, sh, add_comm, add_left_comm, add_assoc]
  have hg : SChain [dn i, up j, up i] ((lcrossL i j).map (whL [] [up i])) [up j, dn i, up i] := by
    simpa using (sChain_lcrossL i j).whisk [] [up i]
  have E := plcL_interchange_hom μ hw (epsP_mem cs i (wt D μ [dn i, up j, up i]))
    (cl_mem_homPar (D := D) (Sc := Sc) hg rfl)
  simp only [plcRight_cl, regionCast_family, List.map_map, parsum_map_whL, parsum_lcrossL] at E
  change capAt cs i μ [] [dn i, up j, up i] ≫ _ = _ at E
  have EE := congrArg (zsign k (ipar D i (wt D μ [dn i, up j, up i]) *
    (D.parity i * D.parity j)) • ·) E
  rw [smul_smul, zsign_mul_self', one_smul] at EE
  exact EE.symm

theorem bendCup_R (i j : I) (μ : X) :
    bendCup cs i j μ (pcuR cs i j (wt D μ [up i])) =
      zsign k (ipar D i (wt D μ [dn i, up j, up i]) * (D.parity i * D.parity j)) • pfR cs i j μ := by
  rw [bendCup_R_expand, ← Category.assoc _ (capAt cs i μ [] [up j, dn i, up i]),
    cross_cap_R, Linear.smul_comp, Linear.comp_smul, ← Category.assoc,
    ← Category.assoc (cupAt cs i μ [dn i] [up j, up i]), cup_cap_F_ctx, Category.id_comp]
  rfl

theorem cap_cap_swap (i j : I) (μ : X) :
    capAt cs i μ [] [up j, dn i, up i] ≫ capAt cs i μ [up j] [] =
      zsign k (ipar D i (wt D μ [up j, dn i, up i]) * ipar D i μ) •
        (capAt cs i μ [dn i, up i, up j] [] ≫ capAt cs i μ [] [up j]) := by
  have hw : wt D μ [up j, dn i, up i] = wt D μ [up j] := by simp [wt, sh]
  have hg : capAt cs i μ [up j] [] ∈
      homPar D Sc μ [up j, dn i, up i] [up j] (ipar D i μ) :=
    plcL_mem _ [up j] [] (epsP_mem cs i _)
  have E := plcL_interchange_hom μ hw (epsP_mem cs i (wt D μ [up j, dn i, up i])) hg
  have hn := plcL_nested μ [dn i, up i] [] [up j] [] (epsP_mem cs i (wt D (wt D μ []) []))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast, LinearMap.id_apply] at hn
  have h0 := plcL_nested μ [] [] [up j] [] (epsP_mem cs i (wt D (wt D μ []) []))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast, LinearMap.id_apply] at h0
  simp only [regionCast_family, plcRight, LinearMap.comp_apply, wordCast] at E
  erw [h0, hn] at E
  exact E

theorem cross_cap_L (i j : I) (μ : X) :
    cl D Sc μ [dn i, up j, up i, dn i, up i] [dn i, up i, up j, dn i, up i]
        (crossL [dn i] j i [dn i, up i]) ≫ capAt cs i μ [dn i, up i, up j] [] =
      zsign k ((D.parity j * D.parity i) * ipar D i μ) •
        (capAt cs i μ [dn i, up j, up i] [] ≫
          cl D Sc μ [dn i, up j, up i] [dn i, up i, up j] (crossL [dn i] j i [])) := by
  have hw : wt D μ [dn i, up i] = wt D μ [] := by simp [wt, sh]
  have hf : SChain [dn i, up j, up i] (crossL [dn i] j i []) [dn i, up i, up j] := by
    simp [crossL, Shape.dom, Shape.cod]
  have E := plcL_interchange_hom μ hw
    (cl_mem_homPar (D := D) (Sc := Sc) (μ := wt D μ [dn i, up i]) hf rfl) (epsP_mem cs i μ)
  simp only [regionCast_cl, plcL_cl, plcRight, LinearMap.comp_apply, wordCast,
    parsum, parity_crossL] at E
  exact E

theorem cup_cap_E_ctx (i j : I) (μ : X) :
    cupAt cs i μ [dn i, up j] [up i] ≫ capAt cs i μ [dn i, up j, up i] [] =
      zsign k (ipar D i μ) • 𝟙 _ := by
  have E := congrArg (plcL D Sc μ [dn i, up j] [] [up i] [up i]) (eq_6_6_a cs i μ)
  have hc : leta cs i μ ∈ homPar D Sc μ [up i] [up i, dn i, up i] _ :=
    plcL_mem _ [] [up i] (etaP_mem cs i _)
  have he : reps cs i μ ∈ homPar D Sc μ [up i, dn i, up i] [up i] _ :=
    plcL_mem _ [up i] [] (epsP_mem cs i _)
  erw [plcL_comp_of_mem μ [dn i, up j] [] hc he, map_smul, plcL_id] at E
  unfold leta reps at E
  have hη := plcL_nested μ [dn i, up j] [] [] [up i]
    (etaP_mem cs i (wt D (wt D μ []) [up i]))
  have hε := plcL_nested μ [dn i, up j] [] [up i] []
    (epsP_mem cs i (wt D (wt D μ []) []))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast, LinearMap.id_apply] at hη hε
  erw [hη, hε] at E
  exact E

theorem ipar_wt_upj (i j : I) (μ : X) : ipar D i (wt D μ [up j]) = ipar D i μ := by
  by_cases hij : i = j
  · subst j; exact ipar_wt_up i μ
  have hp : D.parity i * (D.d i j : ZMod 2) = 0 := by
    rw [← D.dn_cast hij, Int.cast_natCast]
    exact parity_mul_dn D i j
  simp only [ipar, h_wt_upj, Int.cast_sub, mul_add, mul_sub, hp, sub_zero]

theorem bendCup_L (i j : I) (μ : X) :
    bendCup cs i j μ (pcuL cs i j (wt D μ [up i])) =
      zsign k (ipar D i μ * (D.parity i * D.parity j)) • pfL cs i j μ := by
  have hpar : ipar D i (wt D μ [up j, dn i, up i]) = ipar D i μ := by
    have hw : wt D μ [up j, dn i, up i] = wt D μ [up j] := by simp [wt, sh]
    rw [hw, ipar_wt_upj]
  rw [bendCup_L_expand, cap_cap_swap]
  simp only [Linear.comp_smul]
  erw [← Category.assoc _ (capAt cs i μ [dn i, up i, up j] []), cross_cap_L]
  simp only [Linear.smul_comp, Linear.comp_smul]
  erw [← Category.assoc, ← Category.assoc (cupAt cs i μ [dn i, up j] [up i]), cup_cap_E_ctx]
  simp only [Linear.smul_comp, Category.id_comp, smul_smul, hpar]
  rw [← zsign_add, ← zsign_add]
  have hp : ipar D i μ * ipar D i μ + ((D.parity j * D.parity i) * ipar D i μ + ipar D i μ) =
      ipar D i μ * (D.parity i * D.parity j) := by
    rw [zmod2_mul_self]
    generalize ipar D i μ = p; generalize D.parity i = a; generalize D.parity j = b
    revert p a b; decide
  rw [hp]
  rfl

/-- The cup pitchfork at the shifted weight implies the cap pitchfork. -/
theorem cap_of_cup (i j : I) (μ : X)
    (h : pcuL cs i j (wt D μ [up i]) = pcuR cs i j (wt D μ [up i])) :
    pfL cs i j μ = pfR cs i j μ := by
  have E := congrArg (bendCup cs i j μ) h
  have hw : wt D μ [dn i, up j, up i] = wt D μ [up j] := by
    simp [wt, sh, add_comm, add_left_comm]
  rw [bendCup_L, bendCup_R, hw, ipar_wt_upj] at E
  have E' := congrArg (zsign k (ipar D i μ * (D.parity i * D.parity j)) • ·) E
  simpa only [smul_smul, zsign_mul_self', one_smul] using E'

/-- The cap half of Proposition 7.2, with no weight or colour restriction. -/
theorem eq_7_5_a (i j : I) (μ : X) : pfL cs i j μ = pfR cs i j μ := by
  by_cases hij : i = j
  · subst j
    by_cases hh : D.h i μ ≤ -1
    · exact eq_6_1 cs i μ hh
    · apply cap_of_cup
      exact eq_6_2 cs i (wt D μ [up i]) (by rw [h_wt_up]; omega)
  · by_cases hh : D.h i μ ≤ max (D.d i j - 1) 0
    · exact eq_7_1 cs i j μ hij hh
    · apply cap_of_cup
      exact eq_7_2 cs i j (wt D μ [up i]) hij (by rw [h_wt_up]; omega)

end OddMath.SKM
