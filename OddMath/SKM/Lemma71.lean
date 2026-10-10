/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyLeft
import OddMath.SKM.Lemma33Rot

/-!
# Upward strands past leftward caps and cups (Brundan–Ellis, Lemma 7.1)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Lemma 7.1, (7.1)–(7.4)
(TeX labels `pitchforkb`, `easy1`, `easy2`, `critical`, `turn`).

For `i ≠ j`:

* `pfL`, `pfR`: the two sides of (7.1) on `Fᵢ Eⱼ Eᵢ 1_λ`: the upward crossing of `j` and `i`
  followed by `ε'` (at `λ + αⱼ`) on the two left strands, and the leftward crossing of `i` and `j`
  followed by `ε'` (at `λ`) on the two right strands;
* `eq_7_3`: (7.3), for `0 < ⟨hᵢ,λ⟩ < dᵢⱼ`: after the sideways crossing `σ` of `j` and `i` the
  upward `j`-strand passes the leftward cap. As in the paper: insert `-1 = ` (leftward crossing)
  `≫ σ` on `Fᵢ Eᵢ` ((2.12), the sum is empty), pull the `j`-strand past the `ii`-crossing by
  (3.8) (`lemma33_eq8_eq`), and evaluate the correction terms by (2.13) and (2.14);
* `eq_7_1_pos`: (7.1) for `0 < ⟨hᵢ,λ⟩ < dᵢⱼ`, by composing (7.3) with the inverse (1.12).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Finset

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

theorem h_wt_upj (i j : I) (μ : X) : D.h i (wt D μ [up j]) = D.h i μ - D.d i j := by
  simp [wt, sh, Datum.d, map_add]; ring

theorem c_wt_upj (i j : I) (μ : X) : cs.c (wt D μ [up j]) i = Sc.t i j * cs.c μ i := by
  simpa [wt, sh, add_comm] using cs.shift μ i j

/-- The left-hand side of (7.1): on `Fᵢ Eⱼ Eᵢ 1_λ`, the upward crossing of `j` and `i`, then `ε'`
(at `λ + αⱼ`) on the two left strands. -/
def pfL (i j : I) (μ : X) :
    (pres D Sc).obj (ob D μ [dn i, up j, up i]) ⟶ (pres D Sc).obj (ob D μ [up j]) :=
  cl D Sc μ [dn i, up j, up i] [dn i, up i, up j] (crossL [dn i] j i []) ≫
    plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j]))

/-- The right-hand side of (7.1): on `Fᵢ Eⱼ Eᵢ 1_λ`, the leftward crossing of `i` and `j`, then `ε'`
(at `λ`) on the two right strands. -/
def pfR (i j : I) (μ : X) :
    (pres D Sc).obj (ob D μ [dn i, up j, up i]) ⟶ (pres D Sc).obj (ob D μ [up j]) :=
  cl D Sc μ [dn i, up j, up i] [up j, dn i, up i] ((lcrossL i j).map (whL [] [up i])) ≫
    plcL D Sc μ [up j] [] [dn i, up i] [] (epsP cs i μ)

theorem plcL_id (μ : X) (u v s : List (Letter I)) :
    plcL D Sc μ u v s s (𝟙 _) = 𝟙 _ := by
  rw [← cl_nil (wt D μ v) s, plcL_cl, List.map_nil, cl_nil]

theorem term8_eq (i j : I) (r q s : ℕ) :
    term8 i j r q s = (epsL i s).map (whL [up j] []) ++ dotsL [] j [] q ++
      (etaL i r).map (whL [] [up j]) := by
  simp [term8, epsL, etaL, dotsL, whL, List.map_replicate]

/-- A correction term of (3.8), below the leftward crossing and above `ε'`: it factors through the
leftward crossing followed by the dotted rightward cap, and the clockwise dotted bubble. -/
theorem term8_factor (i j : I) (μ : X) (r q s : ℕ) :
    cl D Sc μ [up j, dn i, up i] [up j, up i, dn i] ((lcrossL i i).map (whL [up j] [])) ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (term8 i j r q s) ≫
        plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) =
      plcL D Sc μ [up j] [] [dn i, up i] [] (cl D Sc (wt D μ []) [dn i, up i] []
          (lcrossL i i ++ epsL i s)) ≫
        cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
          plcL D Sc μ [] [up j] [] [] (cl D Sc (wt D μ [up j]) [] [dn i, up i] (etaL i r) ≫
            epsP cs i (wt D μ [up j])) := by
  have h1 : SChain [dn i, up i] (lcrossL i i ++ epsL i s) [] :=
    (sChain_lcrossL i i).append (sChain_epsL i s)
  have h2 : SChain [up j] (dotsL [] j [] q) [up j] := sChain_dotsL [] j [] q
  have h3 : SChain [] (etaL i r) [dn i, up i] := sChain_etaL i r
  rw [plcL_comp_of_mem μ [] [up j] (cl_mem_homPar h3 rfl) (epsP_mem cs i _), plcL_cl, plcL_cl]
  change _ = cl D Sc μ [up j, dn i, up i] [up j] _ ≫ cl D Sc μ [up j] [up j] _ ≫
    cl D Sc μ [up j] [dn i, up i, up j] _ ≫ _
  simp only [← Category.assoc]
  congr 1
  rw [cl_comp (by simpa using (sChain_lcrossL i i).whisk [up j] []) (by
      rw [term8_eq]
      exact ((by simpa using (sChain_epsL i s).whisk [up j] [] :
        SChain [up j, up i, dn i] ((epsL i s).map (whL [up j] [])) [up j]).append h2).append
          (by simpa using h3.whisk [] [up j])),
    cl_comp (by simpa using h1.whisk [up j] []) h2,
    cl_comp ((by simpa using h1.whisk [up j] [] :
      SChain [up j, dn i, up i] ((lcrossL i i ++ epsL i s).map (whL [up j] [])) [up j]).append h2)
      (by simpa using h3.whisk [] [up j]),
    term8_eq, List.map_append]
  simp only [List.append_assoc]

theorem term8_zero_s (i j : I) (μ : X) (r q s : ℕ) (hs : (s : ℤ) < D.h i μ) :
    cl D Sc μ [up j, dn i, up i] [up j, up i, dn i] ((lcrossL i i).map (whL [up j] [])) ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (term8 i j r q s) ≫
        plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) = 0 := by
  rw [term8_factor, eq_2_13_b (Sc := Sc) i (wt D μ []) s (by simpa using hs), map_zero,
    Limits.zero_comp]

theorem term8_zero_r (i j : I) (μ : X) (r q s : ℕ)
    (hr : (r : ℤ) < -D.h i (wt D μ [up j]) - 1) :
    cl D Sc μ [up j, dn i, up i] [up j, up i, dn i] ((lcrossL i i).map (whL [up j] [])) ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (term8 i j r q s) ≫
        plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) = 0 := by
  rw [term8_factor, eq_2_14_c cs i _ r (by omega),
    ite_eq_right (show ¬ ((r : ℤ) = -D.h i (wt D μ [up j]) - 1) by omega), map_zero,
    Limits.comp_zero, Limits.comp_zero]

theorem term8_main (i j : I) (μ : X) (r s : ℕ) (hr : (r : ℤ) = -D.h i (wt D μ [up j]) - 1) :
    cl D Sc μ [up j, dn i, up i] [up j, up i, dn i] ((lcrossL i i).map (whL [up j] [])) ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (term8 i j r 0 s) ≫
        plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) =
      (↑(cs.c (wt D μ [up j]) i)⁻¹ : k) •
        plcL D Sc μ [up j] [] [dn i, up i] [] (cl D Sc (wt D μ []) [dn i, up i] []
          (lcrossL i i ++ epsL i s)) := by
  rw [term8_factor, eq_2_14_c cs i _ r (by omega), ite_eq_left hr, map_smul, plcL_id,
    show dotsL [] j [] 0 = [] from rfl, cl_nil, Linear.comp_smul, Linear.comp_smul]
  erw [Category.id_comp, Category.comp_id]

theorem rhs8_zero (i j : I) (μ : X) (hν : D.h i (wt D μ [up j]) < 0) :
    cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (lemma33_eq8_rhs i j i) ≫
      plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) = 0 := by
  have h1 : SChain [up j, up i, dn i] (crossL [] j i [dn i] ++ (sigmaL i j).map (whL [up i] []))
      [up i, dn i, up j] := by
    refine SChain.append (t' := [up i, up j, dn i]) (by simp [crossL, Shape.dom, Shape.cod]) ?_
    simpa using (sChain_sigmaL i j).whisk [up i] []
  have e : cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (lemma33_eq8_rhs i j i) =
      cl D Sc μ [up j, up i, dn i] [up i, dn i, up j]
          (crossL [] j i [dn i] ++ (sigmaL i j).map (whL [up i] [])) ≫
        plcL D Sc μ [] [up j] [up i, dn i] [dn i, up i]
          (cl D Sc (wt D μ [up j]) [up i, dn i] [dn i, up i] (sigmaL i i)) := by
    rw [plcL_cl]
    exact (cl_comp h1 (by simpa using (sChain_sigmaL i i).whisk [] [up j])).symm
  rw [e, Category.assoc, ← plcL_comp_of_mem μ [] [up j] (cl_mem_homPar (sChain_sigmaL i i) rfl)
    (epsP_mem cs i _), eq_2_14_a cs i _ hν, map_zero, Limits.comp_zero]

/-- **(7.3)** for `0 < ⟨hᵢ,λ⟩ < dᵢⱼ`: the sideways crossing `σ` of `j` and `i` followed by the
left-hand side of (7.1) is `ε'` (at `λ`) to the right of the `j`-strand. -/
theorem eq_7_3 (i j : I) (μ : X) (hij : i ≠ j) (h0 : 0 < D.h i μ) (h1 : D.h i μ < D.d i j) :
    cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫
      pfL cs i j μ = plcL D Sc μ [up j] [] [dn i, up i] [] (epsP cs i μ) := by
  have hν : D.h i (wt D μ [up j]) < 0 := by rw [h_wt_upj]; omega
  have hd := D.dn_cast hij
  -- `1 = -(leftward crossing ≫ σ)` on `Fᵢ Eᵢ 1_λ`
  have hlc : SChain [up j, dn i, up i] ((lcrossL i i).map (whL [up j] [])) [up j, up i, dn i] := by
    simpa using (sChain_lcrossL i i).whisk [up j] []
  have hsii : SChain [up j, up i, dn i] ((sigmaL i i).map (whL [up j] [])) [up j, dn i, up i] := by
    simpa using (sChain_sigmaL i i).whisk [up j] []
  have hsij : SChain [up j, dn i, up i] ((sigmaL i j).map (whL [] [up i])) [dn i, up j, up i] := by
    simpa using (sChain_sigmaL i j).whisk [] [up i]
  have hcr : SChain [dn i, up j, up i] (crossL [dn i] j i []) [dn i, up i, up j] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hid : cl D Sc μ [up j, dn i, up i] [up j, up i, dn i] ((lcrossL i i).map (whL [up j] [])) ≫
      cl D Sc μ [up j, up i, dn i] [up j, dn i, up i] ((sigmaL i i).map (whL [up j] [])) =
      -𝟙 _ := by
    have E := congrArg (plcL D Sc μ [up j] [] [dn i, up i] [dn i, up i])
      (eq_2_12_b Sc i (wt D μ []) )
    rw [show (-D.h i (wt D μ [])).toNat = 0 by simp only [wt_nil]; omega, Finset.range_zero,
      Finset.sum_empty, zero_sub, map_neg, plcL_cl, plcL_cl, List.map_nil, cl_nil] at E
    rw [cl_comp hlc hsii, ← List.map_append]
    exact E
  have e8 := lemma33_eq8_eq (Sc := Sc) i j μ hij
  rw [sub_eq_iff_eq_add, add_assoc] at e8
  have hL : cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫
      pfL cs i j μ = -(cl D Sc μ [up j, dn i, up i] [up j, up i, dn i]
        ((lcrossL i i).map (whL [up j] [])) ≫
          cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (lemma33_eq8_lhs i j i) ≫
            plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j]))) := by
    have e : cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫
        pfL cs i j μ = -((cl D Sc μ [up j, dn i, up i] [up j, up i, dn i]
          ((lcrossL i i).map (whL [up j] [])) ≫
            cl D Sc μ [up j, up i, dn i] [up j, dn i, up i] ((sigmaL i i).map (whL [up j] []))) ≫
          cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫
            pfL cs i j μ) := by
      rw [hid, Preadditive.neg_comp, Category.id_comp, neg_neg]
    rw [e, pfL]
    congr 1
    simp only [Category.assoc]
    congr 1
    rw [← Category.assoc, ← Category.assoc, cl_comp hsii hsij, cl_comp (hsii.append hsij) hcr]
    rfl
  rw [hL, e8]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
    Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul]
  rw [rhs8_zero cs i j μ hν, Limits.comp_zero, add_zero]
  -- the triple sum vanishes
  rw [Finset.sum_eq_zero (s := Finset.Ioo 0 (D.dn i j)) (fun p hp => Finset.sum_eq_zero
    (fun q _ => Finset.sum_eq_zero (fun s hs => by
      rw [Finset.mem_Ioo] at hp
      rw [Finset.mem_range] at hs
      by_cases hsh : (s : ℤ) < D.h i μ
      · rw [term8_zero_s cs i j μ _ _ _ hsh, smul_zero]
      · rw [term8_zero_r cs i j μ _ _ _ (by rw [h_wt_upj]; omega), smul_zero]))), add_zero]
  -- one term of the first sum survives
  set n := (D.h i μ).toNat with hn
  have hn' : (n : ℤ) = D.h i μ := Int.toNat_of_nonneg h0.le
  rw [Finset.sum_eq_single n (fun s hs hsn => by
      rw [Finset.mem_range] at hs
      by_cases hsh : (s : ℤ) < D.h i μ
      · rw [term8_zero_s cs i j μ _ _ _ hsh, smul_zero]
      · rw [term8_zero_r cs i j μ _ _ _ (by rw [h_wt_upj]; omega), smul_zero])
    (fun hn => absurd (Finset.mem_range.2 (by omega)) hn),
    term8_main cs i j μ _ _ (by rw [h_wt_upj]; omega), smul_smul,
    epsP_eq_of_nonneg cs h0.le, map_smul, ← hn]
  rw [← neg_smul]
  congr 1
  rw [c_wt_upj, show ((n : ℕ) : ZMod 2) = ((D.h i μ : ℤ) : ZMod 2) by rw [← hn', Int.cast_natCast],
    mul_inv, Units.val_mul]
  linear_combination (-(zsign k (D.parity i * ↑(D.h i μ))) * (↑(cs.c μ i)⁻¹ : k)) *
    Units.mul_inv (Sc.t i j)

/-- The inverse (1.12) of the sideways crossing `σ` of `j` and `i`, to the left of `Eᵢ`. -/
theorem lcross_sigma_whisk (i j : I) (μ : X) (hij : i ≠ j) :
    cl D Sc μ [dn i, up j, up i] [up j, dn i, up i] ((lcrossL i j).map (whL [] [up i])) ≫
      cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) = 𝟙 _ := by
  have E := congrArg (plcL D Sc μ [] [up i] [dn i, up j] [dn i, up j])
    (cl_invNe₂ (Sc := Sc) i j (wt D μ [up i]) hij)
  rw [plcL_cl, plcL_cl, List.map_nil, cl_nil] at E
  rw [cl_comp (by simpa using (sChain_lcrossL i j).whisk [] [up i])
    (by simpa using (sChain_sigmaL i j).whisk [] [up i]), ← List.map_append]
  exact E

/-- The sideways crossing `σ` of `j` and `i` followed by its inverse (1.12), to the left of `Eᵢ`. -/
theorem sigma_lcross_whisk (i j : I) (μ : X) (hij : i ≠ j) :
    cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫
      cl D Sc μ [dn i, up j, up i] [up j, dn i, up i] ((lcrossL i j).map (whL [] [up i])) = 𝟙 _ := by
  have E := congrArg (plcL D Sc μ [] [up i] [up j, dn i] [up j, dn i])
    (cl_invNe₁ (Sc := Sc) i j (wt D μ [up i]) hij)
  rw [plcL_cl, plcL_cl, List.map_nil, cl_nil] at E
  rw [cl_comp (by simpa using (sChain_sigmaL i j).whisk [] [up i])
    (by simpa using (sChain_lcrossL i j).whisk [] [up i]), ← List.map_append]
  exact E

/-- (7.1) follows from (7.3). -/
theorem eq_7_1_of_eq_7_3 (i j : I) (μ : X) (hij : i ≠ j)
    (h : cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫
      pfL cs i j μ = plcL D Sc μ [up j] [] [dn i, up i] [] (epsP cs i μ)) :
    pfL cs i j μ = pfR cs i j μ := by
  rw [← Category.id_comp (pfL cs i j μ), ← lcross_sigma_whisk i j μ hij, Category.assoc, h]
  rfl

/-- **(7.1)** for `0 < ⟨hᵢ,λ⟩ < dᵢⱼ`. -/
theorem eq_7_1_pos (i j : I) (μ : X) (hij : i ≠ j) (h0 : 0 < D.h i μ) (h1 : D.h i μ < D.d i j) :
    pfL cs i j μ = pfR cs i j μ :=
  eq_7_1_of_eq_7_3 cs i j μ hij (eq_7_3 cs i j μ hij h0 h1)

end OddMath.SKM
