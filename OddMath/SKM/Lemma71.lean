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

/-! ## (7.1) for `⟨hᵢ,λ⟩ ≤ 0` -/

/-- For `⟨hᵢ,λ⟩ ≤ 0`, maps out of `Fᵢ Eⱼ Eᵢ 1_λ` are determined by their composites with
`(↑ ⊗ σ) ≫ (σ ⊗ ↑)` and with `(↑ ⊗ (xⁿ ∘ η)) ≫ (σ ⊗ ↑)` for `n < -⟨hᵢ,λ⟩` (the isomorphisms
(1.12) and (1.14)). -/
theorem ext_FEE (i j : I) (μ : X) (hij : i ≠ j) (hh : D.h i μ ≤ 0) {Z : (pres D Sc).Presented}
    {f g : (pres D Sc).obj (ob D μ [dn i, up j, up i]) ⟶ Z}
    (ha : cl D Sc μ [up j, up i, dn i] [up j, dn i, up i] ((sigmaL i i).map (whL [up j] [])) ≫
      cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫ f =
      cl D Sc μ [up j, up i, dn i] [up j, dn i, up i] ((sigmaL i i).map (whL [up j] [])) ≫
      cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫ g)
    (hb : ∀ n : ℕ, (n : ℤ) < -D.h i μ →
      cl D Sc μ [up j] [up j, dn i, up i] ((etaL i n).map (whL [up j] [])) ≫
        cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫ f =
      cl D Sc μ [up j] [up j, dn i, up i] ((etaL i n).map (whL [up j] [])) ≫
        cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫ g) :
    f = g := by
  have E : cl D Sc μ [up j, dn i, up i] [up j, dn i, up i]
      ((lcrossL i i ++ sigmaL i i).map (whL [up j] [])) =
      ∑ n ∈ range (-D.h i μ).toNat, cl D Sc μ [up j, dn i, up i] [up j, dn i, up i]
        ((dcapL i n ++ etaL i n).map (whL [up j] [])) -
      cl D Sc μ [up j, dn i, up i] [up j, dn i, up i] [] := by
    have E0 := congrArg (plcL D Sc μ [up j] [] [dn i, up i] [dn i, up i])
      (eq_2_12_b Sc i (wt D μ []))
    simp only [map_sub, map_sum, plcL_cl, List.map_nil] at E0
    exact E0
  have hlc : SChain [up j, dn i, up i] ((lcrossL i i).map (whL [up j] [])) [up j, up i, dn i] := by
    simpa using (sChain_lcrossL i i).whisk [up j] []
  have hsii : SChain [up j, up i, dn i] ((sigmaL i i).map (whL [up j] [])) [up j, dn i, up i] := by
    simpa using (sChain_sigmaL i i).whisk [up j] []
  have hdc : ∀ n, SChain [up j, dn i, up i] ((dcapL i n).map (whL [up j] [])) [up j] := fun n => by
    simpa using (sChain_dcapL i n).whisk [up j] []
  have het : ∀ n, SChain [up j] ((etaL i n).map (whL [up j] [])) [up j, dn i, up i] := fun n => by
    simpa using (sChain_etaL i n).whisk [up j] []
  have hid : 𝟙 ((pres D Sc).obj (ob D μ [up j, dn i, up i])) =
      -(cl D Sc μ [up j, dn i, up i] [up j, up i, dn i] ((lcrossL i i).map (whL [up j] [])) ≫
        cl D Sc μ [up j, up i, dn i] [up j, dn i, up i] ((sigmaL i i).map (whL [up j] []))) +
      ∑ n ∈ range (-D.h i μ).toNat,
        cl D Sc μ [up j, dn i, up i] [up j] ((dcapL i n).map (whL [up j] [])) ≫
          cl D Sc μ [up j] [up j, dn i, up i] ((etaL i n).map (whL [up j] [])) := by
    rw [cl_comp hlc hsii, ← List.map_append, E, cl_nil,
      sum_congr rfl fun n _ => cl_comp (hdc n) (het n), ← sum_congr rfl fun n _ =>
        congrArg (cl D Sc μ [up j, dn i, up i] [up j, dn i, up i]) (List.map_append ..)]
    abel
  have key : ∀ φ : (pres D Sc).obj (ob D μ [dn i, up j, up i]) ⟶ Z, φ =
      -(cl D Sc μ [dn i, up j, up i] [up j, dn i, up i] ((lcrossL i j).map (whL [] [up i])) ≫
        cl D Sc μ [up j, dn i, up i] [up j, up i, dn i] ((lcrossL i i).map (whL [up j] [])) ≫
        (cl D Sc μ [up j, up i, dn i] [up j, dn i, up i] ((sigmaL i i).map (whL [up j] [])) ≫
          cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫ φ)) +
      ∑ n ∈ range (-D.h i μ).toNat,
        cl D Sc μ [dn i, up j, up i] [up j, dn i, up i] ((lcrossL i j).map (whL [] [up i])) ≫
          cl D Sc μ [up j, dn i, up i] [up j] ((dcapL i n).map (whL [up j] [])) ≫
          (cl D Sc μ [up j] [up j, dn i, up i] ((etaL i n).map (whL [up j] [])) ≫
            cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫
              φ) := by
    intro φ
    conv_lhs => rw [← Category.id_comp φ, ← lcross_sigma_whisk i j μ hij, Category.assoc,
      ← Category.id_comp (cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] _ ≫ φ), hid]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
      Preadditive.comp_sum, Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]
  rw [key f, key g, ha]
  congr 1
  refine sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  rw [hb n (by omega)]

theorem sigma_eps_h0 (i : I) (μ : X) (hh : D.h i μ = 0) :
    cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ≫ epsP cs i μ =
      (↑(cs.c μ i)⁻¹ : k) • cl D Sc μ [up i, dn i] [] (epsL i 0) := by
  rw [eq_5_17_a, show (D.h i μ).toNat + 1 = 1 by omega, sum_range_one, Nat.cast_zero, mul_zero,
    zsign_zero, one_smul, Nat.cast_zero, neg_zero, zero_sub,
    show (-1 : ℤ) = -D.h i μ - 1 by omega, bubR_eq_c, Linear.comp_smul, Category.comp_id]

theorem term8_factor' (i j : I) (μ : X) (r q s : ℕ) :
    cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (term8 i j r q s) ≫
        plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) =
      plcL D Sc μ [up j] [] [up i, dn i] [] (cl D Sc (wt D μ []) [up i, dn i] [] (epsL i s)) ≫
        cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
          plcL D Sc μ [] [up j] [] [] (cl D Sc (wt D μ [up j]) [] [dn i, up i] (etaL i r) ≫
            epsP cs i (wt D μ [up j])) := by
  have h2 : SChain [up j] (dotsL [] j [] q) [up j] := sChain_dotsL [] j [] q
  have h3 : SChain [] (etaL i r) [dn i, up i] := sChain_etaL i r
  have h1 : SChain [up j, up i, dn i] ((epsL i s).map (whL [up j] [])) [up j] := by
    simpa using (sChain_epsL i s).whisk [up j] []
  rw [plcL_comp_of_mem μ [] [up j] (cl_mem_homPar h3 rfl) (epsP_mem cs i _), plcL_cl, plcL_cl]
  change _ = cl D Sc μ [up j, up i, dn i] [up j] _ ≫ cl D Sc μ [up j] [up j] _ ≫
    cl D Sc μ [up j] [dn i, up i, up j] _ ≫ _
  simp only [← Category.assoc]
  congr 1
  rw [cl_comp h1 h2, cl_comp (h1.append h2) (by simpa using h3.whisk [] [up j]), term8_eq]

theorem term8_zero_r' (i j : I) (μ : X) (r q s : ℕ)
    (hr : (r : ℤ) < -D.h i (wt D μ [up j]) - 1) :
    cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (term8 i j r q s) ≫
        plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) = 0 := by
  rw [term8_factor', eq_2_14_c cs i _ r (by omega),
    ite_eq_right (show ¬ ((r : ℤ) = -D.h i (wt D μ [up j]) - 1) by omega), map_zero,
    Limits.comp_zero, Limits.comp_zero]

theorem pfR_a (i j : I) (μ : X) (hij : i ≠ j) :
    cl D Sc μ [up j, up i, dn i] [up j, dn i, up i] ((sigmaL i i).map (whL [up j] [])) ≫
      cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫
        pfR cs i j μ =
      plcL D Sc μ [up j] [] [up i, dn i] []
        (cl D Sc (wt D μ []) [up i, dn i] [dn i, up i] (sigmaL i i) ≫ epsP cs i (wt D μ [])) := by
  rw [pfR, ← Category.assoc (cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] _),
    sigma_lcross_whisk i j μ hij, Category.id_comp]
  symm
  rw [plcL_comp_of_mem μ [up j] [] (cl_mem_homPar (sChain_sigmaL i i) rfl) (epsP_mem cs i _),
    plcL_cl]
  rfl

theorem pfL_a (i j : I) (μ : X) :
    cl D Sc μ [up j, up i, dn i] [up j, dn i, up i] ((sigmaL i i).map (whL [up j] [])) ≫
      cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫
        pfL cs i j μ =
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (lemma33_eq8_lhs i j i) ≫
        plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) := by
  have hsii : SChain [up j, up i, dn i] ((sigmaL i i).map (whL [up j] [])) [up j, dn i, up i] := by
    simpa using (sChain_sigmaL i i).whisk [up j] []
  have hsij : SChain [up j, dn i, up i] ((sigmaL i j).map (whL [] [up i])) [dn i, up j, up i] := by
    simpa using (sChain_sigmaL i j).whisk [] [up i]
  have hcr : SChain [dn i, up j, up i] (crossL [dn i] j i []) [dn i, up i, up j] := by
    simp [crossL, Shape.dom, Shape.cod]
  rw [pfL, ← Category.assoc, ← Category.assoc, cl_comp hsii hsij,
    cl_comp (hsii.append hsij) hcr]
  rfl

theorem term8_main' (i j : I) (μ : X) (r s : ℕ) (hr : (r : ℤ) = -D.h i (wt D μ [up j]) - 1) :
    cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (term8 i j r 0 s) ≫
        plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) =
      (↑(cs.c (wt D μ [up j]) i)⁻¹ : k) •
        plcL D Sc μ [up j] [] [up i, dn i] [] (cl D Sc (wt D μ []) [up i, dn i] [] (epsL i s)) := by
  rw [term8_factor', eq_2_14_c cs i _ r (by omega), ite_eq_left hr, map_smul, plcL_id,
    show dotsL [] j [] 0 = [] from rfl, cl_nil, Linear.comp_smul, Linear.comp_smul]
  erw [Category.id_comp, Category.comp_id]

theorem rhs8_factor (i j : I) (μ : X) :
    cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (lemma33_eq8_rhs i j i) ≫
      plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) =
    cl D Sc μ [up j, up i, dn i] [up i, dn i, up j]
          (crossL [] j i [dn i] ++ (sigmaL i j).map (whL [up i] [])) ≫
        plcL D Sc μ [] [up j] [up i, dn i] []
          (cl D Sc (wt D μ [up j]) [up i, dn i] [dn i, up i] (sigmaL i i) ≫
            epsP cs i (wt D μ [up j])) := by
  have h1 : SChain [up j, up i, dn i] (crossL [] j i [dn i] ++ (sigmaL i j).map (whL [up i] []))
      [up i, dn i, up j] := by
    refine SChain.append (t' := [up i, up j, dn i]) (by simp [crossL, Shape.dom, Shape.cod]) ?_
    simpa using (sChain_sigmaL i j).whisk [up i] []
  rw [plcL_comp_of_mem μ [] [up j] (cl_mem_homPar (sChain_sigmaL i i) rfl) (epsP_mem cs i _),
    plcL_cl, ← Category.assoc]
  congr 1
  exact (cl_comp h1 (by simpa using (sChain_sigmaL i i).whisk [] [up j])).symm

/-- The first family of test maps of `ext_FEE` agree on the two sides of (7.1) for
`⟨hᵢ,λ⟩ ≤ 0`. -/
theorem pf_a (i j : I) (μ : X) (hij : i ≠ j) (hh : D.h i μ ≤ 0) :
    cl D Sc μ [up j, up i, dn i] [up j, dn i, up i] ((sigmaL i i).map (whL [up j] [])) ≫
      cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫
        pfL cs i j μ =
    cl D Sc μ [up j, up i, dn i] [up j, dn i, up i] ((sigmaL i i).map (whL [up j] [])) ≫
      cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫
        pfR cs i j μ := by
  have hd := D.dn_cast hij
  rw [pfL_a, pfR_a cs i j μ hij]
  have e8 := lemma33_eq8_eq (Sc := Sc) i j μ hij
  rw [sub_eq_iff_eq_add, add_assoc] at e8
  rw [e8]
  simp only [Preadditive.add_comp, Preadditive.sum_comp, Linear.smul_comp]
  have hν := h_wt_upj (D := D) i j μ
  -- the triple sum vanishes
  rw [Finset.sum_eq_zero (s := Finset.Ioo 0 (D.dn i j)) (fun p hp => Finset.sum_eq_zero
    (fun q _ => Finset.sum_eq_zero (fun s hs => by
      rw [Finset.mem_Ioo] at hp
      rw [Finset.mem_range] at hs
      rw [term8_zero_r' cs i j μ _ _ _ (by omega), smul_zero]))), zero_add]
  rcases hh.lt_or_eq with hlt | h0
  · rw [rhs8_zero cs i j μ (by omega), eq_2_14_a cs i _ (by simpa using hlt), map_zero, add_zero,
      Finset.sum_eq_zero (fun s hs => by
        rw [Finset.mem_range] at hs
        rw [term8_zero_r' cs i j μ _ _ _ (by omega), smul_zero])]
  · rw [sigma_eps_h0 cs i (wt D μ []) (by simpa using h0), map_smul]
    by_cases hd0 : D.d i j = 0
    · have hdn : D.dn i j = 0 := by omega
      have hcJI : SChain [up j, up i, dn i] (crossL [] j i [dn i]) [up i, up j, dn i] := by
        simp [crossL, Shape.dom, Shape.cod]
      have hS : SChain [up i, up j, dn i] ((sigmaL i j).map (whL [up i] [])) [up i, dn i, up j] := by
        simpa using (sChain_sigmaL i j).whisk [up i] []
      have hC : SChain [up i, dn i, up j] [([], Shape.cap i, [up j])] [up j] := by
        simp [Shape.dom, Shape.cod]
      have hcIJ : SChain [up i, up j, dn i] [([], Shape.cross i j, [dn i])] [up j, up i, dn i] := by
        simp [Shape.dom, Shape.cod]
      have hC' : SChain [up j, up i, dn i] [([up j], Shape.cap i, [])] [up j] := by
        simp [Shape.dom, Shape.cod]
      have hq := congrArg (plcL D Sc μ [] [dn i] [up j, up i] [up j, up i])
        (cl_quadZero (Sc := Sc) j i (wt D μ [dn i]) hij.symm ((D.d_eq_zero_iff i j).1 hd0))
      rw [plcL_cl, map_smul, plcL_cl, List.map_nil, cl_nil] at hq
      have key : cl D Sc μ [up j, up i, dn i] [up i, dn i, up j]
            (crossL [] j i [dn i] ++ (sigmaL i j).map (whL [up i] [])) ≫
          cl D Sc μ [up i, dn i, up j] [up j] [([], Shape.cap i, [up j])] =
          (Sc.t j i : k) • cl D Sc μ [up j, up i, dn i] [up j] [([up j], Shape.cap i, [])] := by
        rw [← cl_comp hcJI hS, Category.assoc, cl_comp hS hC, eq_2_4_a,
          show ([([], Shape.cross i j, [dn i]), ([up j], Shape.cap i, [])] : List (LayerData I)) =
            [([], Shape.cross i j, [dn i])] ++ [([up j], Shape.cap i, [])] from rfl,
          ← cl_comp hcIJ hC',
          ← Category.assoc, cl_comp hcJI hcIJ]
        erw [hq, Linear.smul_comp, Category.id_comp]
      rw [hdn, Finset.range_zero, Finset.sum_empty, zero_add, rhs8_factor,
        sigma_eps_h0 cs i _ (by omega), map_smul, Linear.comp_smul, plcL_cl, plcL_cl]
      erw [key]
      rw [smul_smul, c_wt_upj, Sc.t_symm_of_d_eq_zero i j hd0]
      congr 1
      rw [mul_inv, Units.val_mul, wt_nil]
      linear_combination (↑(cs.c μ i)⁻¹ : k) * Units.inv_mul (Sc.t j i)
    · rw [rhs8_zero cs i j μ (by omega), add_zero,
        Finset.sum_eq_single 0 (fun s hs hs0 => by
          rw [Finset.mem_range] at hs
          rw [term8_zero_r' cs i j μ _ _ _ (by omega), smul_zero])
          (fun h => absurd (Finset.mem_range.2 (by omega)) h),
        term8_main' cs i j μ _ _ (by omega), smul_smul, c_wt_upj, Nat.cast_zero, mul_zero,
        zsign_zero, one_mul]
      congr 1
      rw [mul_inv, Units.val_mul, wt_nil]
      linear_combination (↑(cs.c μ i)⁻¹ : k) * Units.mul_inv (Sc.t i j)

theorem pfR_b (i j : I) (μ : X) (hij : i ≠ j) (n : ℕ) :
    cl D Sc μ [up j] [up j, dn i, up i] ((etaL i n).map (whL [up j] [])) ≫
      cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫
        pfR cs i j μ =
      plcL D Sc μ [up j] [] [] []
        (cl D Sc (wt D μ []) [] [dn i, up i] (etaL i n) ≫ epsP cs i (wt D μ [])) := by
  rw [pfR, ← Category.assoc (cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] _),
    sigma_lcross_whisk i j μ hij, Category.id_comp]
  symm
  rw [plcL_comp_of_mem μ [up j] [] (cl_mem_homPar (sChain_etaL i n) rfl) (epsP_mem cs i _),
    plcL_cl]
  rfl

/-- A clockwise bubble to the left of the `j`-strand, followed by a map on the `j`-strand. -/
theorem bub_factor (i j : I) (μ : X) (m : ℕ) {B : List (LayerData I)} (hB : SChain [up j] B [up j]) :
    cl D Sc μ [up j] [dn i, up i, up j]
        ((etaL i m).map (whL [] [up j]) ++ B.map (whL [dn i, up i] [])) ≫
      plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) =
    zsign k (ipar D i (wt D μ [up j]) * parsum D B) •
      (plcL D Sc μ [] [up j] [] [] (cl D Sc (wt D μ [up j]) [] [dn i, up i] (etaL i m) ≫
        epsP cs i (wt D μ [up j])) ≫ cl D Sc μ [up j] [up j] B) := by
  have h3 : SChain [] (etaL i m) [dn i, up i] := sChain_etaL i m
  have hI := plcL_left_interchange (Sc := Sc) μ [up j] (epsP_mem cs i (wt D μ [up j])) hB
  simp only [map_whL_nil_nil] at hI
  rw [← cl_comp (by simpa using h3.whisk [] [up j]) (by simpa using hB.whisk [dn i, up i] []),
    Category.assoc]
  erw [show cl D Sc μ [dn i, up i, up j] [dn i, up i, up j] (B.map (whL [dn i, up i] [])) ≫
      plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) =
      zsign k (ipar D i (wt D μ [up j]) * parsum D B) •
        (plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) ≫
          cl D Sc μ [up j] [up j] B) by
    erw [hI, smul_smul, zsign_mul_self', one_smul]; rfl]
  rw [Linear.comp_smul, ← Category.assoc, plcL_comp_of_mem μ [] [up j] (cl_mem_homPar h3 rfl)
    (epsP_mem cs i _), plcL_cl]
  rfl

theorem pfL_b_reduce (i j : I) (μ : X) (hij : i ≠ j) (n : ℕ) :
    cl D Sc μ [up j] [up j, dn i, up i] ((etaL i n).map (whL [up j] [])) ≫
      cl D Sc μ [up j, dn i, up i] [dn i, up j, up i] ((sigmaL i j).map (whL [] [up i])) ≫
        pfL cs i j μ =
    cl D Sc μ [up j] [dn i, up i, up j]
        ((etaL i n).map (whL [] [up j]) ++ crossL [dn i] i j [] ++ crossL [dn i] j i []) ≫
      plcL D Sc μ [] [up j] [dn i, up i] [] (epsP cs i (wt D μ [up j])) := by
  have het : SChain [up j] ((etaL i n).map (whL [up j] [])) [up j, dn i, up i] := by
    simpa using (sChain_etaL i n).whisk [up j] []
  have hsij : SChain [up j, dn i, up i] ((sigmaL i j).map (whL [] [up i])) [dn i, up j, up i] := by
    simpa using (sChain_sigmaL i j).whisk [] [up i]
  have hcr : SChain [dn i, up j, up i] (crossL [dn i] j i []) [dn i, up i, up j] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hcup : SChain [up j] [([up j], Shape.cup i, [])] [up j, dn i, up i] := by
    simp [Shape.dom, Shape.cod]
  have hdA : SChain [dn i, up j, up i] (dotsL [dn i, up j] i [] n) [dn i, up j, up i] :=
    sChain_dotsL [dn i, up j] i [] n
  have hP : SChain [up j] ([([up j], Shape.cup i, [])] ++ (sigmaL i j).map (whL [] [up i]))
      [dn i, up j, up i] := hcup.append hsij
  have hP' : SChain [up j] [([], Shape.cup i, [up j]), ([dn i], Shape.cross i j, [])]
      [dn i, up j, up i] := by simp [Shape.dom, Shape.cod]
  -- the dots pass the sideways crossing
  have eA : cl D Sc μ [up j] [dn i, up i, up j]
      ((etaL i n).map (whL [up j] []) ++ (sigmaL i j).map (whL [] [up i]) ++
        crossL [dn i] j i []) =
      zsign k (parsum D (sigmaL i j) * parsum D (dotsL [] i [] n)) •
        cl D Sc μ [up j] [dn i, up i, up j]
          ([([up j], Shape.cup i, [])] ++ (sigmaL i j).map (whL [] [up i]) ++
            dotsL [dn i, up j] i [] n ++ crossL [dn i] j i []) := by
    have hI := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := [up j]) (T := [dn i, up i, up j])
      [([up j], Shape.cup i, [])] (crossL [dn i] j i []) (sChain_sigmaL i j)
      (sChain_dotsL [] i [] n)
    simp only [List.nil_append, List.append_nil] at hI
    have e1 : (etaL i n).map (whL [up j] []) = [([up j], Shape.cup i, [])] ++
        (dotsL [] i [] n).map (whL [up j, dn i] []) := by
      simp [etaL, dotsL, whL, List.map_replicate]
    have e2 : (dotsL [] i [] n).map (whL [dn i, up j] []) = dotsL [dn i, up j] i [] n := by
      simp [dotsL, whL, List.map_replicate]
    rw [e1, ← e2, hI, smul_smul, zsign_mul_self', one_smul]
  -- (2.4)
  have eB : cl D Sc μ [up j] [dn i, up i, up j]
      ([([up j], Shape.cup i, [])] ++ (sigmaL i j).map (whL [] [up i]) ++
        dotsL [dn i, up j] i [] n ++ crossL [dn i] j i []) =
      cl D Sc μ [up j] [dn i, up i, up j]
        ([([], Shape.cup i, [up j]), ([dn i], Shape.cross i j, [])] ++
          dotsL [dn i, up j] i [] n ++ crossL [dn i] j i []) := by
    rw [List.append_assoc _ (dotsL _ _ _ _), List.append_assoc [_, _],
      ← cl_comp hP (hdA.append hcr), ← cl_comp hP' (hdA.append hcr)]
    congr 1
    exact eq_2_4_b Sc i j μ
  -- the dots pass the upward crossing
  have eC : cl D Sc μ [up j] [dn i, up i, up j]
      ([([], Shape.cup i, [up j]), ([dn i], Shape.cross i j, [])] ++
          dotsL [dn i, up j] i [] n ++ crossL [dn i] j i []) =
      zsign k (D.parity i * D.parity j * n) •
        cl D Sc μ [up j] [dn i, up i, up j]
          ((etaL i n).map (whL [] [up j]) ++ crossL [dn i] i j [] ++ crossL [dn i] j i []) := by
    have h31 := congrArg (plcL D Sc μ [dn i] [] [up i, up j] [up j, up i])
      (lemma31_eq1_ne Sc i j (wt D μ []) hij n)
    rw [map_smul, plcL_cl, plcL_cl] at h31
    have e3 : (etaL i n).map (whL [] [up j]) ++ crossL [dn i] i j [] =
        [([], Shape.cup i, [up j])] ++ (dotsL [] i [up j] n ++ crossL [] i j []).map (whL [dn i] []) := by
      simp [etaL, dotsL, crossL, whL, List.map_replicate]
    have e4 : [([], Shape.cup i, [up j]), ([dn i], Shape.cross i j, [])] ++
        dotsL [dn i, up j] i [] n = [([], Shape.cup i, [up j])] ++
          (crossL [] i j [] ++ dotsL [up j] i [] n).map (whL [dn i] []) := by
      simp [dotsL, crossL, whL, List.map_replicate]
    have hc0 : SChain [up j] [([], Shape.cup i, [up j])] [dn i, up i, up j] := by
      simp [Shape.dom, Shape.cod]
    have hX : SChain [dn i, up i, up j] ((dotsL [] i [up j] n ++ crossL [] i j []).map
        (whL [dn i] [])) [dn i, up j, up i] := by
      simpa using ((sChain_dotsL [] i [up j] n).append
        (by simp [crossL, Shape.dom, Shape.cod] : SChain [up i, up j] (crossL [] i j [])
          [up j, up i])).whisk [dn i] []
    have hY : SChain [dn i, up i, up j] ((crossL [] i j [] ++ dotsL [up j] i [] n).map
        (whL [dn i] [])) [dn i, up j, up i] := by
      simpa using ((by simp [crossL, Shape.dom, Shape.cod] : SChain [up i, up j] (crossL [] i j [])
          [up j, up i]).append (sChain_dotsL [up j] i [] n)).whisk [dn i] []
    rw [e4, e3]
    refine cl_append_congr _ (hc0.append hY) (hc0.append hX) hcr _ ?_
    refine cl_prefix_congr _ hc0 hY hX _ ?_
    rw [show cl D Sc μ [dn i, up i, up j] [dn i, up j, up i]
      ((dotsL [] i [up j] n ++ crossL [] i j []).map (whL [dn i] [])) = _ from h31, smul_smul,
      zsign_mul_self', one_smul]
    rfl
  rw [pfL, ← Category.assoc, ← Category.assoc, cl_comp het hsij,
    cl_comp (het.append hsij) hcr, eA, eB, eC, smul_smul, Linear.smul_comp]
  rw [← zsign_add, parsum_sigmaL, parsum_dotsL]
  generalize D.parity i = a
  generalize D.parity j = b
  generalize (n : ZMod 2) = c
  rw [show a * b * (c * a) + a * b * c = 0 by revert a b c; decide, zsign_zero, one_smul]

end OddMath.SKM
