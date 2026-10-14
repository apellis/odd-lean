/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.AltBraid

/-!
# A braid relation with one leftward downward strand ([BE2] §7)

For `i ≠ j`, the braid relation on `[dn i, up j, up a] → [up a, up j, dn i]` with two leftward
crossings and one upward crossing. It is the rotation of the upward braid relation (1.9) for
the colours `(j, a, i)` by the left cup `η'`: the pitchfork relation (7.5) moves the crossings
through the cup, and the left adjunction (6.6) cancels the cup. Used for the case `i = k ≠ j`
of [BE2] Prop 7.6 in `OddMath.SKM.AlternativeBraid`.
-/

noncomputable section
namespace OddMath.SKM.AltBraid
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- The left-cup pitchfork (7.5) with one spectator on the right. -/
theorem cup_pf_right (i j a : I) (μ : X) :
    cupAt cs i μ [] [up j, up a] ≫
      cl D Sc μ [up i, dn i, up j, up a] [up i, up j, dn i, up a]
        ((lcrossL i j).map (whL [up i] [up a])) =
    cupAt cs i μ [up j] [up a] ≫
      cl D Sc μ [up j, up i, dn i, up a] [up i, up j, dn i, up a]
        (crossL [] j i [dn i, up a]) := by
  have E := congrArg (plcL D Sc μ [] [up a] [up j] [up i, up j, dn i])
    (eq_7_5_b cs i j (wt D μ [up a]))
  have ht : SChain [up j, up i, dn i] (crossL [] j i [dn i]) [up i, up j, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hx := (sChain_lcrossL i j).wh [up i] [] rfl rfl
  unfold pcuL pcuR at E
  erw [plcL_comp_of_mem μ [] [up a] (plcL_mem _ [up j] [] (etaP_mem cs i _))
      (cl_mem_homPar ht rfl),
    plcL_comp_of_mem μ [] [up a] (plcL_mem _ [] [up j] (etaP_mem cs i _))
      (cl_mem_homPar hx rfl), plcL_cl, plcL_cl] at E
  have hL := plcL_nested μ [] [up a] [up j] [] (etaP_mem cs i (wt D (wt D μ [up a]) []))
  have hR := plcL_nested μ [] [up a] [] [up j] (etaP_mem cs i (wt D (wt D μ [up a]) [up j]))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast,
    LinearMap.id_apply] at hL hR
  erw [hL, hR] at E
  simpa only [cupAt, lcrossL, List.map_map, crossL, List.map_cons, List.map_nil, whL,
    List.cons_append,
    List.nil_append, List.append_nil] using E.symm

/-- The same pitchfork with one spectator on the left. -/
theorem cup_pf_left (i j a : I) (μ : X) :
    cupAt cs i μ [up a] [up j] ≫
      cl D Sc μ [up a, up i, dn i, up j] [up a, up i, up j, dn i]
        ((lcrossL i j).map (whL [up a, up i] [])) =
    cupAt cs i μ [up a, up j] [] ≫
      cl D Sc μ [up a, up j, up i, dn i] [up a, up i, up j, dn i]
        (crossL [up a] j i [dn i]) := by
  have E := congrArg (plcL D Sc μ [up a] [] [up j] [up i, up j, dn i])
    (eq_7_5_b cs i j (wt D μ []))
  have ht : SChain [up j, up i, dn i] (crossL [] j i [dn i]) [up i, up j, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hx := (sChain_lcrossL i j).wh [up i] [] rfl rfl
  unfold pcuL pcuR at E
  erw [plcL_comp_of_mem μ [up a] [] (plcL_mem _ [up j] [] (etaP_mem cs i _))
      (cl_mem_homPar ht rfl),
    plcL_comp_of_mem μ [up a] [] (plcL_mem _ [] [up j] (etaP_mem cs i _))
      (cl_mem_homPar hx rfl), plcL_cl, plcL_cl] at E
  have hL := plcL_nested μ [up a] [] [up j] [] (etaP_mem cs i (wt D (wt D μ []) []))
  have hR := plcL_nested μ [up a] [] [] [up j] (etaP_mem cs i (wt D (wt D μ []) [up j]))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast,
    LinearMap.id_apply] at hL hR
  erw [hL, hR] at E
  simpa only [cupAt, lcrossL, List.map_map, crossL, List.map_cons, List.map_nil, whL,
    List.cons_append,
    List.nil_append, List.append_nil] using E.symm

/-- The left-adjoint mixed braid, before cancellation of unequal crossings. -/
def leftBraidL (i j a : I) : List (LayerData I) :=
  (lcrossL i j).map (whL [] [up a]) ++
    (lcrossL i a).map (whL [up j] []) ++ crossL [] j a [dn i]
def leftBraidR (i j a : I) : List (LayerData I) :=
  crossL [dn i] j a [] ++ (lcrossL i a).map (whL [] [up j]) ++
    (lcrossL i j).map (whL [up a] [])

theorem leftBraidL_chain (i j a : I) :
    SChain [dn i, up j, up a] (leftBraidL i j a) [up a, up j, dn i] := by
  exact ((sChain_lcrossL i j).wh [] [up a] rfl rfl).append
    (((sChain_lcrossL i a).wh [up j] [] rfl rfl).append
      (by simp [crossL, Shape.dom, Shape.cod]))
theorem leftBraidR_chain (i j a : I) :
    SChain [dn i, up j, up a] (leftBraidR i j a) [up a, up j, dn i] := by
  exact (show SChain [dn i, up j, up a] (crossL [dn i] j a []) [dn i, up a, up j] by
    simp [crossL, Shape.dom, Shape.cod]).append
    (((sChain_lcrossL i a).wh [] [up j] rfl rfl).append
      ((sChain_lcrossL i j).wh [up a] [] rfl rfl))

theorem crossing_exchange (i j a : I) (μ : X) :
    cl D Sc μ [up j, up i, dn i, up a] [up i, up j, dn i, up a]
        (crossL [] j i [dn i, up a]) ≫
      cl D Sc μ [up i, up j, dn i, up a] [up i, up j, up a, dn i]
        ((lcrossL i a).map (whL [up i, up j] [])) =
    zsign k ((D.parity j * D.parity i) * (D.parity i * D.parity a)) •
      (cl D Sc μ [up j, up i, dn i, up a] [up j, up i, up a, dn i]
          ((lcrossL i a).map (whL [up j, up i] [])) ≫
        cl D Sc μ [up j, up i, up a, dn i] [up i, up j, up a, dn i]
          (crossL [] j i [up a, dn i])) := by
  have ht : SChain [up j, up i] (crossL [] j i []) [up i, up j] := by
    simp [crossL, Shape.dom, Shape.cod]
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ)
    (S := [up j, up i, dn i, up a]) (T := [up i, up j, up a, dn i]) [] [] ht (sChain_lcrossL i a)
  simp only [List.nil_append, List.append_nil] at E
  erw [← cl_comp (ht.wh [] [dn i, up a] rfl rfl) ((sChain_lcrossL i a).wh [up i, up j] [] rfl rfl),
    ← cl_comp ((sChain_lcrossL i a).wh [up j, up i] [] rfl rfl)
      (ht.wh [] [up a, dn i] rfl rfl)] at E
  simpa [parsum, crossL, lcrossL, whL, Shape.parity, cupAt,
    LinearMap.comp_apply] using E

theorem cup_cross_left (i j a : I) (μ : X) :
    cupAt cs i μ [] [up j, up a] ≫
      cl D Sc μ [up i, dn i, up j, up a] [up i, dn i, up a, up j]
        (crossL [up i, dn i] j a []) =
    zsign k (ipar D i (wt D μ [up j, up a]) * (D.parity j * D.parity a)) •
      (cl D Sc μ [up j, up a] [up a, up j] (crossL [] j a []) ≫
        cupAt cs i μ [] [up a, up j]) := by
  have hw : wt D μ [up j, up a] = wt D μ [up a, up j] := by
    simp [wt, sh, add_comm, add_left_comm, add_assoc]
  have ht : SChain [up j, up a] (crossL [] j a []) [up a, up j] := by
    simp [crossL, Shape.dom, Shape.cod]
  have E := plcL_interchange_hom μ hw (etaP_mem cs i (wt D μ [up j, up a]))
    (cl_mem_homPar (D := D) (Sc := Sc) ht rfl)
  simp only [plcRight_cl, regionCast_family] at E
  simpa [parsum, crossL, lcrossL, whL, Shape.parity, cupAt,
    LinearMap.comp_apply] using E

theorem cup_cross_right (i j a : I) (μ : X) :
    cl D Sc μ [up j, up a] [up a, up j] (crossL [] j a []) ≫
      cupAt cs i μ [up a, up j] [] =
    zsign k ((D.parity j * D.parity a) * ipar D i μ) •
      (cupAt cs i μ [up j, up a] [] ≫
        cl D Sc μ [up j, up a, up i, dn i] [up a, up j, up i, dn i]
          (crossL [] j a [up i, dn i])) := by
  have hw : wt D μ [] = wt D μ [up i, dn i] := by simp [wt, sh]
  have ht : SChain [up j, up a] (crossL [] j a []) [up a, up j] := by
    simp [crossL, Shape.dom, Shape.cod]
  have E := plcL_interchange_hom μ hw
    (cl_mem_homPar (D := D) (Sc := Sc) (μ := wt D μ []) ht rfl) (etaP_mem cs i μ)
  simp only [regionCast_cl, plcRight, wordCast] at E
  erw [plcL_cl, plcL_cl] at E
  change cl D Sc μ [up j, up a] [up a, up j] (crossL [] j a []) ≫
      cupAt cs i μ [up a, up j] [] =
    zsign k (parsum D (crossL [] j a []) * ipar D i μ) •
      (cupAt cs i μ [up j, up a] [] ≫
        cl D Sc μ [up j, up a, up i, dn i] [up a, up j, up i, dn i]
          (crossL [] j a [up i, dn i])) at E
  simpa only [parsum, crossL, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, Shape.parity] using E

theorem cup_image_L (i j a : I) (μ : X) :
    cupAt cs i μ [] [up j, up a] ≫
      cl D Sc μ [up i, dn i, up j, up a] [up i, up a, up j, dn i]
        ((leftBraidL i j a).map (whL [up i] [])) =
    zsign k ((D.parity j * D.parity i) * (D.parity i * D.parity a)) •
      (cupAt cs i μ [up j, up a] [] ≫
        cl D Sc μ [up j, up a, up i, dn i] [up i, up a, up j, dn i]
          (crossL [up j] a i [dn i] ++ crossL [] j i [up a, dn i] ++
            crossL [up i] j a [dn i])) := by
  have h1 : SChain [up i, dn i, up j, up a]
      ((lcrossL i j).map (whL [up i] [up a])) [up i, up j, dn i, up a] :=
    (sChain_lcrossL i j).wh [up i] [up a] rfl rfl
  have h2 : SChain [up i, up j, dn i, up a]
      ((lcrossL i a).map (whL [up i, up j] [])) [up i, up j, up a, dn i] :=
    (sChain_lcrossL i a).wh [up i, up j] [] rfl rfl
  have h3 : SChain [up i, up j, up a, dn i]
      (crossL [up i] j a [dn i]) [up i, up a, up j, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have he : cl D Sc μ [up i, dn i, up j, up a] [up i, up a, up j, dn i]
      ((leftBraidL i j a).map (whL [up i] [])) =
      cl D Sc μ [up i, dn i, up j, up a] [up i, up j, dn i, up a]
          ((lcrossL i j).map (whL [up i] [up a])) ≫
        cl D Sc μ [up i, up j, dn i, up a] [up i, up j, up a, dn i]
          ((lcrossL i a).map (whL [up i, up j] [])) ≫
        cl D Sc μ [up i, up j, up a, dn i] [up i, up a, up j, dn i]
          (crossL [up i] j a [dn i]) := by
    rw [cl_comp h2 h3, cl_comp h1 (h2.append h3)]
    rfl
  rw [he, ← Category.assoc, ← Category.assoc, cup_pf_right]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (cl D Sc μ _ _ (crossL [up i] j a [dn i])),
    crossing_exchange, Linear.smul_comp, Linear.comp_smul]
  simp only [← Category.assoc]
  rw [cup_pf_left]
  congr 1
  have t1 : SChain [up j, up a, up i, dn i]
      (crossL [up j] a i [dn i]) [up j, up i, up a, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have t2 : SChain [up j, up i, up a, dn i]
      (crossL [] j i [up a, dn i]) [up i, up j, up a, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  rw [Category.assoc, Category.assoc, cl_comp t2 h3, cl_comp t1 (t2.append h3)]
  simp only [List.append_assoc]

theorem cup_image_R (i j a : I) (μ : X) :
    cupAt cs i μ [] [up j, up a] ≫
      cl D Sc μ [up i, dn i, up j, up a] [up i, up a, up j, dn i]
        ((leftBraidR i j a).map (whL [up i] [])) =
    zsign k ((D.parity a * D.parity i) * (D.parity i * D.parity j)) •
      (cupAt cs i μ [up j, up a] [] ≫
        cl D Sc μ [up j, up a, up i, dn i] [up i, up a, up j, dn i]
          (crossL [] j a [up i, dn i] ++ crossL [up a] j i [dn i] ++
            crossL [] a i [up j, dn i])) := by
  have h1 : SChain [up i, dn i, up j, up a]
      (crossL [up i, dn i] j a []) [up i, dn i, up a, up j] := by
    simp [crossL, Shape.dom, Shape.cod]
  have h2 : SChain [up i, dn i, up a, up j]
      ((lcrossL i a).map (whL [up i] [up j])) [up i, up a, dn i, up j] :=
    (sChain_lcrossL i a).wh [up i] [up j] rfl rfl
  have h3 : SChain [up i, up a, dn i, up j]
      ((lcrossL i j).map (whL [up i, up a] [])) [up i, up a, up j, dn i] :=
    (sChain_lcrossL i j).wh [up i, up a] [] rfl rfl
  have he : cl D Sc μ [up i, dn i, up j, up a] [up i, up a, up j, dn i]
      ((leftBraidR i j a).map (whL [up i] [])) =
      cl D Sc μ [up i, dn i, up j, up a] [up i, dn i, up a, up j]
          (crossL [up i, dn i] j a []) ≫
        cl D Sc μ [up i, dn i, up a, up j] [up i, up a, dn i, up j]
          ((lcrossL i a).map (whL [up i] [up j])) ≫
        cl D Sc μ [up i, up a, dn i, up j] [up i, up a, up j, dn i]
          ((lcrossL i j).map (whL [up i, up a] [])) := by
    rw [cl_comp h2 h3, cl_comp h1 (h2.append h3)]
    rfl
  rw [he, ← Category.assoc, ← Category.assoc, cup_cross_left]
  simp only [Linear.smul_comp, Category.assoc]
  rw [← Category.assoc (cupAt cs i μ [] [up a, up j]), cup_pf_right]
  simp only [Category.assoc]
  rw [crossing_exchange, Linear.comp_smul, Linear.comp_smul]
  rw [← Category.assoc (cupAt cs i μ [up a] [up j]), cup_pf_left]
  simp only [← Category.assoc]
  rw [cup_cross_right]
  simp only [Linear.smul_comp, smul_smul]
  have hp : ipar D i (wt D μ [up j, up a]) = ipar D i μ := by
    rw [show wt D μ [up j, up a] = wt D (wt D μ [up a]) [up j] from rfl,
      ipar_wt_upj, ipar_wt_upj]
  rw [hp]
  have hs : zsign k (ipar D i μ * (D.parity j * D.parity a)) *
      (zsign k ((D.parity a * D.parity i) * (D.parity i * D.parity j)) *
        zsign k ((D.parity j * D.parity a) * ipar D i μ)) =
      zsign k ((D.parity a * D.parity i) * (D.parity i * D.parity j)) := by
    rw [mul_comm (D.parity j * D.parity a), mul_left_comm, zsign_mul_self', mul_one]
  rw [hs]
  congr 1
  have t1 : SChain [up j, up a, up i, dn i]
      (crossL [] j a [up i, dn i]) [up a, up j, up i, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have t2 : SChain [up a, up j, up i, dn i]
      (crossL [up a] j i [dn i]) [up a, up i, up j, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have t3 : SChain [up a, up i, up j, dn i]
      (crossL [] a i [up j, dn i]) [up i, up a, up j, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  rw [Category.assoc, Category.assoc, cl_comp t2 t3, cl_comp t1 (t2.append t3)]
  simp only [List.append_assoc]

/-- The left adjunction triangle (6.6) on `Fᵢ`, with two upward spectators. -/
theorem cup_cap_cancel (i j a : I) (μ : X) :
    cupAt cs i μ [dn i] [up j, up a] ≫
      capAt cs i μ [] [dn i, up j, up a] = 𝟙 _ := by
  have E := congrArg (plcL D Sc μ [] [up j, up a] [dn i] [dn i])
    (eq_6_6_b cs i (wt D μ [up j, up a]))
  have hc : retaF cs i (wt D μ [up j, up a]) ∈
      homPar D Sc (wt D μ [up j, up a]) [dn i] [dn i, up i, dn i] _ :=
    plcL_mem _ [dn i] [] (etaP_mem cs i _)
  have he : lepsF cs i (wt D μ [up j, up a]) ∈
      homPar D Sc (wt D μ [up j, up a]) [dn i, up i, dn i] [dn i] _ :=
    plcL_mem _ [] [dn i] (epsP_mem cs i _)
  rw [plcL_comp_of_mem μ [] [up j, up a] hc he, plcL_id] at E
  unfold retaF lepsF at E
  have hη := plcL_nested μ [] [up j, up a] [dn i] []
    (etaP_mem cs i (wt D (wt D μ [up j, up a]) []))
  have hε := plcL_nested μ [] [up j, up a] [] [dn i]
    (epsP_mem cs i (wt D (wt D μ [up j, up a]) [dn i]))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast,
    LinearMap.id_apply] at hη hε
  change _ ≫ _ = _ at E
  erw [hη, hε] at E
  exact E

/-- Explicit inverse computation for the left-cup test, including its super sign. -/
theorem cup_test_recover (i j a : I) (μ : X) {L : List (LayerData I)}
    (hL : SChain [dn i, up j, up a] L [up a, up j, dn i]) :
    plcL D Sc μ [dn i] [] [up j, up a] [up i, up a, up j, dn i]
        (cupAt cs i μ [] [up j, up a] ≫
          cl D Sc μ [up i, dn i, up j, up a] [up i, up a, up j, dn i]
            (L.map (whL [up i] []))) ≫
      capAt cs i μ [] [up a, up j, dn i] =
    zsign k (ipar D i (wt D μ [dn i, up j, up a]) * parsum D L) •
      cl D Sc μ [dn i, up j, up a] [up a, up j, dn i] L := by
  have hc : cupAt cs i (wt D μ []) [] [up j, up a] ∈
      homPar D Sc (wt D μ []) [up j, up a] [up i, dn i, up j, up a] _ :=
    plcL_mem _ [] [up j, up a] (etaP_mem cs i _)
  have hl : SChain [up i, dn i, up j, up a] (L.map (whL [up i] []))
      [up i, up a, up j, dn i] := hL.wh [up i] [] rfl rfl
  erw [plcL_comp_of_mem μ [dn i] [] hc (cl_mem_homPar hl rfl), plcL_cl]
  have hn := plcL_nested μ [dn i] [] [] [up j, up a]
    (etaP_mem cs i (wt D (wt D μ []) [up j, up a]))
  simp only [regionCast_family, List.cons_append, List.nil_append, wordCast,
    LinearMap.id_apply] at hn
  erw [hn]
  simp only [map_whL_map_whL, List.cons_append, List.nil_append, List.append_nil]
  have hw : wt D μ [dn i, up j, up a] = wt D μ [up a, up j, dn i] :=
    (SChain.wt_eq D μ hL).symm
  have E := plcL_interchange_hom μ hw
    (epsP_mem cs i (wt D μ [dn i, up j, up a]))
    (cl_mem_homPar (D := D) (Sc := Sc) hL rfl)
  simp only [plcRight_cl, regionCast_family, List.nil_append] at E
  erw [plcRight_cl] at E
  have E' := congrArg
    (zsign k (ipar D i (wt D μ [dn i, up j, up a]) * parsum D L) • ·) E
  rw [smul_smul, zsign_mul_self', one_smul] at E'
  have ex : cl D Sc μ [dn i, up i, dn i, up j, up a] [dn i, up i, up a, up j, dn i]
        (L.map (whL [dn i, up i] [])) ≫ capAt cs i μ [] [up a, up j, dn i] =
      zsign k (ipar D i (wt D μ [dn i, up j, up a]) * parsum D L) •
        (capAt cs i μ [] [dn i, up j, up a] ≫
          cl D Sc μ [dn i, up j, up a] [up a, up j, dn i] L) := by
    simpa only [capAt, show whL ([] : List (Letter I)) [] = id from funext whL_nil_nil,
      List.map_id, List.cons_append, List.nil_append] using E'.symm
  rw [Category.assoc, ex, Linear.comp_smul, ← Category.assoc]
  erw [cup_cap_cancel]
  erw [Category.id_comp]

theorem cup_test_injective (i j a : I) (μ : X) {L M : List (LayerData I)}
    (hL : SChain [dn i, up j, up a] L [up a, up j, dn i])
    (hM : SChain [dn i, up j, up a] M [up a, up j, dn i])
    (hp : parsum D L = parsum D M)
    (h : cupAt cs i μ [] [up j, up a] ≫
        cl D Sc μ [up i, dn i, up j, up a] [up i, up a, up j, dn i]
          (L.map (whL [up i] [])) =
      cupAt cs i μ [] [up j, up a] ≫
        cl D Sc μ [up i, dn i, up j, up a] [up i, up a, up j, dn i]
          (M.map (whL [up i] []))) :
    cl D Sc μ [dn i, up j, up a] [up a, up j, dn i] L =
      cl D Sc μ [dn i, up j, up a] [up a, up j, dn i] M := by
  have E := congrArg (fun f =>
    plcL D Sc μ [dn i] [] [up j, up a] [up i, up a, up j, dn i] f ≫
      capAt cs i μ [] [up a, up j, dn i]) h
  erw [cup_test_recover cs i j a μ hL, cup_test_recover cs i j a μ hM, hp] at E
  have E' := congrArg
    (zsign k (ipar D i (wt D μ [dn i, up j, up a]) * parsum D M) • ·) E
  simpa only [smul_smul, zsign_mul_self', one_smul] using E'

include cs in
/-- Left-adjoint rotation of the upward braid. The outer upward colours are distinct,
so the upward braid relation (1.9) has no correction term, even when `a = i`. -/
theorem left_braid (i j a : I) (μ : X) (hij : i ≠ j) :
    cl D Sc μ [dn i, up j, up a] [up a, up j, dn i] (leftBraidL i j a) =
      cl D Sc μ [dn i, up j, up a] [up a, up j, dn i] (leftBraidR i j a) := by
  apply cup_test_injective cs i j a μ (leftBraidL_chain i j a) (leftBraidR_chain i j a)
  · simp only [leftBraidL, leftBraidR, parsum_append, parsum_map_whL, parsum_lcrossL]
    simp only [parsum, crossL, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, Shape.parity]
    abel
  · rw [cup_image_L, cup_image_R]
    have hs : (D.parity j * D.parity i) * (D.parity i * D.parity a) =
        (D.parity a * D.parity i) * (D.parity i * D.parity j) := by ring
    rw [hs]
    have E := congrArg (plcL D Sc μ [] [dn i] [up j, up a, up i] [up i, up a, up j])
      (cl_braid Sc j a i (wt D μ [dn i]) (fun h => hij h.1.symm))
    simp only [plcL_cl] at E
    have eb : cl D Sc μ [up j, up a, up i, dn i] [up i, up a, up j, dn i]
        (crossL [up j] a i [dn i] ++ crossL [] j i [up a, dn i] ++
          crossL [up i] j a [dn i]) =
      cl D Sc μ [up j, up a, up i, dn i] [up i, up a, up j, dn i]
        (crossL [] j a [up i, dn i] ++ crossL [up a] j i [dn i] ++
          crossL [] a i [up j, dn i]) := by
      simpa only [crossL, List.map_append, List.map_cons, List.map_nil, whL,
        List.cons_append, List.nil_append, List.append_nil] using E.symm
    rw [eb]

end OddMath.SKM.AltBraid
