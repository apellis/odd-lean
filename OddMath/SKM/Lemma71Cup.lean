/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Lemma71

/-!
# Upward strands past leftward cups

The cup relation of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Lemma 7.1, (7.2).
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- The left-hand side of (7.2): a cup to the right, followed by the upward crossing. -/
def pcuL (i j : I) (μ : X) :
    (pres D Sc).obj (ob D μ [up j]) ⟶ (pres D Sc).obj (ob D μ [up i, up j, dn i]) :=
  plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
    cl D Sc μ [up j, up i, dn i] [up i, up j, dn i] (crossL [] j i [dn i])

/-- The right-hand side of (7.2): a cup to the left, followed by the leftward crossing. -/
def pcuR (i j : I) (μ : X) :
    (pres D Sc).obj (ob D μ [up j]) ⟶ (pres D Sc).obj (ob D μ [up i, up j, dn i]) :=
  plcL D Sc μ [] [up j] [] [up i, dn i] (etaP cs i (wt D μ [up j])) ≫
    cl D Sc μ [up i, dn i, up j] [up i, up j, dn i] ((lcrossL i j).map (whL [up i] []))

/-- Sideways crossing on the rightmost pair. -/
abbrev pcuS (i j : I) (μ : X) :=
  cl D Sc μ [up i, up j, dn i] [up i, dn i, up j] ((sigmaL i j).map (whL [up i] []))

/-- Its inverse, for distinct colours. -/
abbrev pcuT (i j : I) (μ : X) :=
  cl D Sc μ [up i, dn i, up j] [up i, up j, dn i] ((lcrossL i j).map (whL [up i] []))

/-- The first test map in the inversion relation on the leftmost pair. -/
abbrev pcuA (i j : I) (μ : X) :=
  cl D Sc μ [up i, dn i, up j] [dn i, up i, up j] ((sigmaL i i).map (whL [] [up j]))

/-- The dotted-cap test maps in the inversion relation on the leftmost pair. -/
abbrev pcuB (i j : I) (μ : X) (n : ℕ) :=
  cl D Sc μ [up i, dn i, up j] [up j] ((epsL i n).map (whL [] [up j]))

theorem pcuS_T (i j : I) (μ : X) (hij : i ≠ j) : pcuS (Sc := Sc) i j μ ≫ pcuT i j μ = 𝟙 _ := by
  have E := congrArg (plcL D Sc μ [up i] [] [up j, dn i] [up j, dn i])
    (cl_invNe₁ Sc i j (wt D μ []) hij)
  simp only [plcL_cl, cl_nil, plcL_id] at E
  rw [pcuS, pcuT, cl_comp (by simpa using (sChain_sigmaL i j).whisk [up i] [])
    (by simpa using (sChain_lcrossL i j).whisk [up i] []), ← List.map_append]
  exact E

theorem pcuT_S (i j : I) (μ : X) (hij : i ≠ j) : pcuT (Sc := Sc) i j μ ≫ pcuS i j μ = 𝟙 _ := by
  have E := congrArg (plcL D Sc μ [up i] [] [dn i, up j] [dn i, up j])
    (cl_invNe₂ Sc i j (wt D μ []) hij)
  simp only [plcL_cl, cl_nil, plcL_id] at E
  rw [pcuS, pcuT, cl_comp (by simpa using (sChain_lcrossL i j).whisk [up i] [])
    (by simpa using (sChain_sigmaL i j).whisk [up i] []), ← List.map_append]
  exact E

/-- The components of (1.13) determine a morphism into `Eᵢ Fᵢ Eⱼ`. -/
theorem ext_EFEj (i j : I) (μ : X) (hh : 0 ≤ D.h i (wt D μ [up j]))
    {Z : (pres D Sc).Presented} {f g : Z ⟶ (pres D Sc).obj (ob D μ [up i, dn i, up j])}
    (h₁ : f ≫ pcuA i j μ = g ≫ pcuA i j μ)
    (h₂ : ∀ n : ℕ, (n : ℤ) < D.h i (wt D μ [up j]) →
      f ≫ pcuB i j μ n = g ≫ pcuB i j μ n) : f = g := by
  have E : -cl D Sc μ [up i, dn i, up j] [up i, dn i, up j]
        ((sigmaL i i ++ lcrossL i i).map (whL [] [up j])) +
      ∑ n ∈ range (D.h i (wt D μ [up j])).toNat, cl D Sc μ [up i, dn i, up j] [up i, dn i, up j]
        ((epsL i n ++ dcupL i n).map (whL [] [up j])) =
      cl D Sc μ [up i, dn i, up j] [up i, dn i, up j] [] := by
    have E0 := congrArg (plcL D Sc μ [] [up j] [up i, dn i] [up i, dn i])
      (cl_invP₁ Sc i (wt D μ [up j]) hh)
    simp only [map_add, map_neg, map_sum, plcL_cl] at E0
    exact E0
  have hs : SChain [up i, dn i, up j] ((sigmaL i i).map (whL [] [up j])) [dn i, up i, up j] := by
    simpa using (sChain_sigmaL i i).whisk [] [up j]
  have hl : SChain [dn i, up i, up j] ((lcrossL i i).map (whL [] [up j])) [up i, dn i, up j] := by
    simpa using (sChain_lcrossL i i).whisk [] [up j]
  have he : ∀ n, SChain [up i, dn i, up j] ((epsL i n).map (whL [] [up j])) [up j] := fun n => by
    simpa using (sChain_epsL i n).whisk [] [up j]
  have hd : ∀ n, SChain [up j] ((dcupL i n).map (whL [] [up j])) [up i, dn i, up j] := fun n => by
    simpa using (sChain_dcupL i n).whisk [] [up j]
  have hid : 𝟙 ((pres D Sc).obj (ob D μ [up i, dn i, up j])) =
      -(pcuA i j μ ≫ cl D Sc μ [dn i, up i, up j] [up i, dn i, up j]
        ((lcrossL i i).map (whL [] [up j]))) +
      ∑ n ∈ range (D.h i (wt D μ [up j])).toNat,
        pcuB i j μ n ≫ cl D Sc μ [up j] [up i, dn i, up j] ((dcupL i n).map (whL [] [up j])) := by
    rw [← cl_nil μ [up i, dn i, up j], ← E, cl_comp hs hl, List.map_append]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [cl_comp (he n) (hd n), List.map_append]
  rw [← Category.comp_id f, ← Category.comp_id g, hid]
  simp only [Preadditive.comp_add, Preadditive.comp_neg, Preadditive.comp_sum, ← Category.assoc, h₁]
  congr 1
  refine sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  rw [h₂ n (by omega)]

/-- The test maps for (7.2), including the isomorphism (1.12). -/
theorem ext_EEF (i j : I) (μ : X) (hij : i ≠ j) (hh : D.d i j ≤ D.h i μ)
    {Z : (pres D Sc).Presented} {f g : Z ⟶ (pres D Sc).obj (ob D μ [up i, up j, dn i])}
    (ha : f ≫ pcuS i j μ ≫ pcuA i j μ = g ≫ pcuS i j μ ≫ pcuA i j μ)
    (hb : ∀ n : ℕ, (n : ℤ) < D.h i (wt D μ [up j]) →
      f ≫ pcuS i j μ ≫ pcuB i j μ n = g ≫ pcuS i j μ ≫ pcuB i j μ n) : f = g := by
  have E : f ≫ pcuS i j μ = g ≫ pcuS i j μ :=
    ext_EFEj i j μ (by rw [h_wt_upj]; omega) (by simpa only [Category.assoc] using ha)
      (fun n hn => by simpa only [Category.assoc] using hb n hn)
  have E' := congrArg (· ≫ pcuT i j μ) E
  simpa only [Category.assoc, pcuS_T i j μ hij, Category.comp_id] using E'

theorem pcuR_a (i j : I) (μ : X) (hij : i ≠ j) :
    pcuR cs i j μ ≫ pcuS i j μ ≫ pcuA i j μ =
      plcL D Sc μ [] [up j] [] [dn i, up i]
        (etaP cs i (wt D μ [up j]) ≫ cl D Sc (wt D μ [up j]) [up i, dn i] [dn i, up i] (sigmaL i i)) := by
  rw [pcuR, Category.assoc, ← Category.assoc (pcuT i j μ), pcuT_S i j μ hij, Category.id_comp]
  rw [plcL_comp_of_mem μ [] [up j] (etaP_mem cs i _) (cl_mem_homPar (sChain_sigmaL i i) rfl), plcL_cl]
  rfl

theorem pcuR_b (i j : I) (μ : X) (hij : i ≠ j) (n : ℕ) :
    pcuR cs i j μ ≫ pcuS i j μ ≫ pcuB i j μ n =
      plcL D Sc μ [] [up j] [] []
        (etaP cs i (wt D μ [up j]) ≫ cl D Sc (wt D μ [up j]) [up i, dn i] [] (epsL i n)) := by
  rw [pcuR, Category.assoc, ← Category.assoc (pcuT i j μ), pcuT_S i j μ hij, Category.id_comp]
  rw [plcL_comp_of_mem μ [] [up j] (etaP_mem cs i _) (cl_mem_homPar (sChain_epsL i n) rfl), plcL_cl]
  rfl

theorem pcuL_a (i j : I) (μ : X) :
    pcuL cs i j μ ≫ pcuS i j μ ≫ pcuA i j μ =
      plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
        cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (lemma33_eq8_rhs i j i) := by
  have hc : SChain [up j, up i, dn i] (crossL [] j i [dn i]) [up i, up j, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hs : SChain [up i, up j, dn i] ((sigmaL i j).map (whL [up i] [])) [up i, dn i, up j] := by
    simpa using (sChain_sigmaL i j).whisk [up i] []
  have hs' : SChain [up i, dn i, up j] ((sigmaL i i).map (whL [] [up j])) [dn i, up i, up j] := by
    simpa using (sChain_sigmaL i i).whisk [] [up j]
  rw [pcuL, Category.assoc, pcuS, pcuA, ← Category.assoc (cl D Sc μ _ _ _),
    cl_comp hc hs, cl_comp (hc.append hs) hs']
  rfl

theorem pcu_term8_factor (i j : I) (μ : X) (r q s : ℕ) :
    plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (term8 i j r q s) =
    plcL D Sc μ [up j] [] [] []
        (etaP cs i (wt D μ []) ≫ cl D Sc (wt D μ []) [up i, dn i] [] (epsL i s)) ≫
      cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
        cl D Sc μ [up j] [dn i, up i, up j] ((etaL i r).map (whL [] [up j])) := by
  have he : SChain [up j, up i, dn i] ((epsL i s).map (whL [up j] [])) [up j] := by
    simpa using (sChain_epsL i s).whisk [up j] []
  have hd := sChain_dotsL [] j [] q
  have hu : SChain [up j] ((etaL i r).map (whL [] [up j])) [dn i, up i, up j] := by
    simpa using (sChain_etaL i r).whisk [] [up j]
  rw [plcL_comp_of_mem μ [up j] [] (etaP_mem cs i _) (cl_mem_homPar (sChain_epsL i s) rfl),
    plcL_cl, Category.assoc, term8_eq]
  erw [cl_comp hd hu, cl_comp he (hd.append hu)]
  simp only [List.append_assoc]

theorem pcu_term8_zero (i j : I) (μ : X) (r q s : ℕ) (hs : (s : ℤ) < D.h i μ - 1) :
    plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (term8 i j r q s) = 0 := by
  rw [pcu_term8_factor, eq_2_13_c cs i _ s (by simpa only [wt_nil] using (by omega : (s : ℤ) < D.h i μ)),
    ite_eq_right (show ¬ (s : ℤ) = D.h i (wt D μ []) - 1 by simp only [wt_nil]; omega),
    map_zero, Limits.zero_comp]

theorem pcu_lhs8_zero (i j : I) (μ : X) (hh : 0 < D.h i μ) :
    plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (lemma33_eq8_lhs i j i) = 0 := by
  have hs : SChain [up j, up i, dn i] ((sigmaL i i).map (whL [up j] [])) [up j, dn i, up i] := by
    simpa using (sChain_sigmaL i i).whisk [up j] []
  have ht : SChain [up j, dn i, up i]
      ((sigmaL i j).map (whL [] [up i]) ++ crossL [dn i] j i []) [dn i, up i, up j] :=
    (by simpa using (sChain_sigmaL i j).whisk [] [up i] :
      SChain [up j, dn i, up i] ((sigmaL i j).map (whL [] [up i])) [dn i, up j, up i]).append
      (by simp [crossL, Shape.dom, Shape.cod])
  simp only [lemma33_eq8_lhs, List.append_assoc]
  rw [← cl_comp hs ht, ← Category.assoc]
  have E := plcL_comp_of_mem (D := D) (Sc := Sc) μ [up j] [] (etaP_mem cs i (wt D μ []))
    (cl_mem_homPar (sChain_sigmaL i i) rfl)
  rw [plcL_cl] at E
  erw [← E, eq_2_13_a cs i (wt D μ []) hh, map_zero, Limits.zero_comp]

/-- The first test maps agree strictly above the boundary `h = dᵢⱼ`. -/
theorem pcu_a_gt (i j : I) (μ : X) (hij : i ≠ j) (hh : D.d i j < D.h i μ) :
    pcuL cs i j μ ≫ pcuS i j μ ≫ pcuA i j μ =
      pcuR cs i j μ ≫ pcuS i j μ ≫ pcuA i j μ := by
  have hd := D.dn_cast hij
  have E := lemma33_eq8_eq (Sc := Sc) i j μ hij
  have E' := congrArg (plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫ ·) E
  simp only [Preadditive.comp_sub, Preadditive.comp_add, Preadditive.comp_sum, Linear.comp_smul] at E'
  rw [pcu_lhs8_zero cs i j μ (by omega)] at E'
  have hz : ∀ r q s : ℕ, s < D.dn i j →
      plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
        cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (term8 i j r q s) = 0 :=
    fun r q s hs => pcu_term8_zero cs i j μ r q s (by omega)
  rw [sum_eq_zero (fun s hs => by rw [hz _ _ _ (mem_range.1 hs), smul_zero]),
    sum_eq_zero (fun p hp => sum_eq_zero (fun q _ => sum_eq_zero (fun s hs => by
      rw [hz _ _ _ (by have := (mem_Ioo.1 hp).2; have := mem_range.1 hs; omega), smul_zero]))),
    zero_add, zero_sub, neg_eq_zero] at E'
  rw [pcuL_a, E', pcuR_a cs i j μ hij, eq_2_13_a cs i _ (by rw [h_wt_upj]; omega), map_zero]

theorem pcuL_b_reduce (i j : I) (μ : X) (hij : i ≠ j) (n : ℕ) :
    pcuL cs i j μ ≫ pcuS i j μ ≫ pcuB i j μ n =
      plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
        cl D Sc μ [up j, up i, dn i] [up j]
          (crossL [] j i [dn i] ++ crossL [] i j [dn i] ++ (epsL i n).map (whL [up j] [])) := by
  have hji : SChain [up j, up i, dn i] (crossL [] j i [dn i]) [up i, up j, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hijc : SChain [up i, up j, dn i] (crossL [] i j [dn i]) [up j, up i, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hs : SChain [up i, up j, dn i] ((sigmaL i j).map (whL [up i] [])) [up i, dn i, up j] := by
    simpa using (sChain_sigmaL i j).whisk [up i] []
  have he : SChain [up i, dn i, up j] ((epsL i n).map (whL [] [up j])) [up j] := by
    simpa using (sChain_epsL i n).whisk [] [up j]
  have hcap : SChain [up i, dn i, up j] [([], Shape.cap i, [up j])] [up j] := by
    simp [Shape.dom, Shape.cod]
  have hcap' : SChain [up j, up i, dn i] [([up j], Shape.cap i, [])] [up j] := by
    simp [Shape.dom, Shape.cod]
  have hdot : SChain [up i, up j, dn i] (dotsL [] i [up j, dn i] n) [up i, up j, dn i] :=
    sChain_dotsL [] i [up j, dn i] n
  have eA : cl D Sc μ [up i, up j, dn i] [up j]
      ((sigmaL i j).map (whL [up i] []) ++ (epsL i n).map (whL [] [up j])) =
      zsign k (parsum D (dotsL [] i [] n) * parsum D (sigmaL i j)) •
        cl D Sc μ [up i, up j, dn i] [up j]
          (dotsL [] i [up j, dn i] n ++ (sigmaL i j).map (whL [up i] []) ++
            [([], Shape.cap i, [up j])]) := by
    have hI := cl_interchange (D := D) (Sc := Sc) (μ := μ)
      (S := [up i, up j, dn i]) (T := [up j]) [] [([], Shape.cap i, [up j])]
      (sChain_dotsL [] i [] n) (sChain_sigmaL i j)
    simp only [List.nil_append, List.append_nil] at hI
    have e1 : (epsL i n).map (whL [] [up j]) =
        (dotsL [] i [] n).map (whL [] [dn i, up j]) ++ [([], Shape.cap i, [up j])] := by
      simp [epsL, dotsL, whL, List.map_replicate]
    have e2 : (dotsL [] i [] n).map (whL [] [up j, dn i]) = dotsL [] i [up j, dn i] n := by
      simp [dotsL, whL, List.map_replicate]
    rw [e1, ← e2, hI, smul_smul, zsign_mul_self', one_smul]
    simp only [List.append_assoc]
  have eB : cl D Sc μ [up i, up j, dn i] [up j]
      (dotsL [] i [up j, dn i] n ++ (sigmaL i j).map (whL [up i] []) ++
        [([], Shape.cap i, [up j])]) =
      cl D Sc μ [up i, up j, dn i] [up j]
        (dotsL [] i [up j, dn i] n ++ crossL [] i j [dn i] ++ [([up j], Shape.cap i, [])]) := by
    simp only [List.append_assoc]
    rw [← cl_comp hdot (hs.append hcap), ← cl_comp hdot (hijc.append hcap')]
    congr 1
    exact eq_2_4_a Sc i j μ
  have eC : cl D Sc μ [up i, up j, dn i] [up j]
      (dotsL [] i [up j, dn i] n ++ crossL [] i j [dn i] ++ [([up j], Shape.cap i, [])]) =
      zsign k (D.parity i * D.parity j * n) •
        cl D Sc μ [up i, up j, dn i] [up j]
          (crossL [] i j [dn i] ++ (epsL i n).map (whL [up j] [])) := by
    have h31 := congrArg (plcL D Sc μ [] [dn i] [up i, up j] [up j, up i])
      (lemma31_eq1_ne Sc i j (wt D μ [dn i]) hij n)
    simp only [map_smul, plcL_cl] at h31
    have hX : SChain [up i, up j, dn i]
        ((dotsL [] i [up j] n ++ crossL [] i j []).map (whL [] [dn i])) [up j, up i, dn i] := by
      simpa using ((sChain_dotsL [] i [up j] n).append
        (by simp [crossL, Shape.dom, Shape.cod] : SChain [up i, up j] (crossL [] i j [])
          [up j, up i])).whisk [] [dn i]
    have hY : SChain [up i, up j, dn i]
        ((crossL [] i j [] ++ dotsL [up j] i [] n).map (whL [] [dn i])) [up j, up i, dn i] := by
      simpa using ((by simp [crossL, Shape.dom, Shape.cod] : SChain [up i, up j] (crossL [] i j [])
          [up j, up i]).append (sChain_dotsL [up j] i [] n)).whisk [] [dn i]
    have H := cl_append_congr (D := D) (Sc := Sc) (μ := μ) _ hX hY hcap'
      (zsign k (D.parity i * D.parity j * n)) h31
    simpa [epsL, dotsL, crossL, whL, List.map_replicate] using H
  rw [pcuL, pcuS, pcuB, Category.assoc, cl_comp hs he, eA, eB, eC,
    smul_smul, parsum_dotsL, parsum_sigmaL]
  have hp : ((n : ZMod 2) * D.parity i) * (D.parity i * D.parity j) =
      D.parity i * D.parity j * n := by
    generalize D.parity i = a
    generalize D.parity j = b
    generalize (n : ZMod 2) = c
    revert a b c
    decide
  rw [hp, zsign_mul_self', one_smul, cl_comp hji (hijc.append
    (by simpa using (sChain_epsL i n).whisk [up j] []))]
  simp only [List.append_assoc]

theorem dots_epsL (i : I) (n m : ℕ) (w : List (Letter I)) :
    dotsL w i [dn i] m ++ (epsL i n).map (whL w []) = (epsL i (m + n)).map (whL w []) := by
  simp [epsL, dotsL, whL, List.map_replicate, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]

theorem pcu_bubble (i j : I) (μ : X) (n m : ℕ) :
    plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
      cl D Sc μ [up j, up i, dn i] [up j, up i, dn i] (dotsL [up j] i [dn i] m) ≫
        cl D Sc μ [up j, up i, dn i] [up j] ((epsL i n).map (whL [up j] [])) =
      plcL D Sc μ [up j] [] [] []
        (etaP cs i (wt D μ []) ≫ cl D Sc (wt D μ []) [up i, dn i] [] (epsL i (m + n))) := by
  have he : SChain [up j, up i, dn i] ((epsL i n).map (whL [up j] [])) [up j] := by
    simpa using (sChain_epsL i n).whisk [up j] []
  have hd : SChain [up j, up i, dn i] (dotsL [up j] i [dn i] m) [up j, up i, dn i] :=
    sChain_dotsL [up j] i [dn i] m
  rw [cl_comp hd he, dots_epsL,
    plcL_comp_of_mem μ [up j] [] (etaP_mem cs i _) (cl_mem_homPar (sChain_epsL i (m + n)) rfl), plcL_cl]
  rfl

theorem pcu_pair_zero (i j : I) (μ : X) (n m q : ℕ) (hm : (m + n : ℕ) < D.h i μ - 1) :
    plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
      cl D Sc μ [up j, up i, dn i] [up j, up i, dn i]
        (dotsL [up j] i [dn i] m ++ dotsL [] j [up i, dn i] q) ≫
      cl D Sc μ [up j, up i, dn i] [up j] ((epsL i n).map (whL [up j] [])) = 0 := by
  have hd : SChain [up j, up i, dn i] (dotsL [up j] i [dn i] m) [up j, up i, dn i] :=
    sChain_dotsL [up j] i [dn i] m
  have hj : SChain [up j, up i, dn i] (dotsL [] j [up i, dn i] q) [up j, up i, dn i] :=
    sChain_dotsL [] j [up i, dn i] q
  have hi := plcL_right_interchange (Sc := Sc) μ [up j]
    (cl_mem_homPar (sChain_epsL i n) rfl) (sChain_dotsL [] j [] q)
  simp only [plcL_cl, map_whL_nil_nil] at hi
  have ej : (dotsL [] j [] q).map (whL [] [up i, dn i]) = dotsL [] j [up i, dn i] q := by
    simp [dotsL, whL, List.map_replicate]
  rw [ej] at hi
  have hi' : cl D Sc μ [up j, up i, dn i] [up j, up i, dn i] (dotsL [] j [up i, dn i] q) ≫
      cl D Sc μ [up j, up i, dn i] [up j] ((epsL i n).map (whL [up j] [])) =
      zsign k (parsum D (epsL i n) * parsum D (dotsL [] j [] q)) •
        (cl D Sc μ [up j, up i, dn i] [up j] ((epsL i n).map (whL [up j] [])) ≫
          cl D Sc μ [up j] [up j] (dotsL [] j [] q)) := by
    erw [hi, smul_smul, zsign_mul_self', one_smul]
    rfl
  have hbub := pcu_bubble cs i j μ n m
  simp only [← Category.assoc] at hbub
  rw [← cl_comp hd hj, Category.assoc, hi', Linear.comp_smul, Linear.comp_smul,
    ← Category.assoc, ← Category.assoc, hbub,
    eq_2_13_c cs i _ (m + n) (by simpa only [wt_nil] using (by omega : (m + n : ℕ) < D.h i μ)),
    ite_eq_right (show ¬ ((m + n : ℕ) : ℤ) = D.h i (wt D μ []) - 1 by simp only [wt_nil]; omega),
    map_zero, Limits.zero_comp, smul_zero]

set_option maxHeartbeats 800000 in
theorem pcu_b (i j : I) (μ : X) (hij : i ≠ j) (n : ℕ)
    (hn : (n : ℤ) < D.h i (wt D μ [up j])) :
    pcuL cs i j μ ≫ pcuS i j μ ≫ pcuB i j μ n =
      pcuR cs i j μ ≫ pcuS i j μ ≫ pcuB i j μ n := by
  have hd := D.dn_cast hij
  have hv := h_wt_upj (D := D) i j μ
  have he : SChain [up j, up i, dn i] ((epsL i n).map (whL [up j] [])) [up j] := by
    simpa using (sChain_epsL i n).whisk [up j] []
  have hc : SChain [up j, up i, dn i]
      (crossL [] j i [dn i] ++ crossL [] i j [dn i]) [up j, up i, dn i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hb (m : ℕ) :
      plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
        cl D Sc μ [up j, up i, dn i] [up j] ((epsL i m).map (whL [up j] [])) =
      plcL D Sc μ [up j] [] [] []
        (etaP cs i (wt D μ []) ≫ cl D Sc (wt D μ []) [up i, dn i] [] (epsL i m)) := by
    rw [plcL_comp_of_mem μ [up j] [] (etaP_mem cs i _) (cl_mem_homPar (sChain_epsL i m) rfl), plcL_cl]
    rfl
  have fin : (Sc.t i j : k) • plcL D Sc μ [up j] [] [] []
        (etaP cs i (wt D μ []) ≫ cl D Sc (wt D μ []) [up i, dn i] [] (epsL i (D.dn i j + n))) =
      plcL D Sc μ [] [up j] [] []
        (etaP cs i (wt D μ [up j]) ≫ cl D Sc (wt D μ [up j]) [up i, dn i] [] (epsL i n)) := by
    rw [eq_2_13_c cs i _ (D.dn i j + n) (by simp only [wt_nil]; push_cast; omega),
      eq_2_13_c cs i _ n hn]
    by_cases hm : (n : ℤ) = D.h i (wt D μ [up j]) - 1
    · rw [ite_eq_left hm, ite_eq_left (by simp only [wt_nil]; push_cast; omega),
        map_smul, map_smul, plcL_id, plcL_id, smul_smul, c_wt_upj, Units.val_mul, wt_nil]
      rfl
    · rw [ite_eq_right hm, ite_eq_right (by simp only [wt_nil]; push_cast; omega),
        map_zero, map_zero, smul_zero]
  rw [pcuL_b_reduce cs i j μ hij, pcuR_b cs i j μ hij, ← fin, ← cl_comp hc he]
  by_cases hd0 : D.d j i = 0
  · have hd0' : D.d i j = 0 := (D.d_eq_zero_iff j i).1 hd0
    have hdn : D.dn i j = 0 := by omega
    have hq := congrArg (plcL D Sc μ [] [dn i] [up j, up i] [up j, up i])
      (cl_quadZero (Sc := Sc) j i (wt D μ [dn i]) hij.symm hd0)
    simp only [map_smul, plcL_cl, cl_nil, plcL_id] at hq
    erw [hq, Linear.smul_comp, Linear.comp_smul, Category.id_comp]
    rw [hb, Sc.t_symm_of_d_eq_zero j i hd0, hdn, zero_add]
  · have hd0' : D.d i j ≠ 0 := fun h => hd0 ((D.d_eq_zero_iff i j).1 h)
    have hq := congrArg (plcL D Sc μ [] [dn i] [up j, up i] [up j, up i])
      (cl_quadNe (Sc := Sc) j i (wt D μ [dn i]) hij.symm hd0)
    simp only [map_add, map_smul, map_sum, plcL_cl] at hq
    erw [hq]
    simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.sum_comp,
      Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul]
    simp only [dotsL, List.map_append, List.map_replicate, whL,
      List.nil_append, List.append_nil, List.cons_append]
    have main := pcu_bubble cs i j μ n (D.dn i j)
    have hz (m q : ℕ) (hm : m < D.dn i j) :=
      pcu_pair_zero cs i j μ n m q (by push_cast; omega)
    simp only [dotsL] at main hz
    erw [main, hz 0 (D.dn j i) (by omega), smul_zero, zero_add,
      sum_eq_zero (fun p _ => sum_eq_zero (fun q hq => by
        erw [hz q p (mem_Ioo.1 hq).2, smul_zero])), add_zero]
    rfl

theorem eta_sigma_h0 (i : I) (μ : X) (hh : D.h i μ = 0) :
    etaP cs i μ ≫ cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) =
      (-(zsign k (D.parity i) * (cs.c μ i : k))) • cl D Sc μ [] [dn i, up i] (etaL i 0) := by
  rw [eq_5_17_b, show (-D.h i μ).toNat + 1 = 1 by omega, sum_range_one]
  simp only [Nat.zero_add, Nat.cast_one, mul_one, Nat.cast_zero, neg_zero, zero_sub]
  rw [show (-1 : ℤ) = D.h i μ - 1 by omega, bubL_eq_c,
    Linear.smul_comp, Category.id_comp, smul_smul, neg_smul]

/-- At the boundary, only the last dotted-cap correction term survives. -/
theorem pcu_term8_top (i j : I) (μ : X) (s : ℕ) (hs : (s : ℤ) = D.h i μ - 1) :
    plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (term8 i j 0 0 s) =
      (cs.c μ i : k) • cl D Sc μ [up j] [dn i, up i, up j] ((etaL i 0).map (whL [] [up j])) := by
  rw [pcu_term8_factor, eq_2_13_c cs i _ s (by simpa only [wt_nil] using (by omega : (s : ℤ) < D.h i μ)),
    ite_eq_left (by simpa only [wt_nil] using hs), map_smul, plcL_id,
    show dotsL [] j [] 0 = [] from rfl, cl_nil, Linear.smul_comp, Category.id_comp]
  erw [Category.id_comp]
  rfl

theorem pcu_lhs8_factor (i j : I) (μ : X) :
    plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (lemma33_eq8_lhs i j i) =
    plcL D Sc μ [up j] [] [] [dn i, up i]
        (etaP cs i (wt D μ []) ≫ cl D Sc (wt D μ []) [up i, dn i] [dn i, up i] (sigmaL i i)) ≫
      cl D Sc μ [up j, dn i, up i] [dn i, up i, up j]
        ((sigmaL i j).map (whL [] [up i]) ++ crossL [dn i] j i []) := by
  have hs : SChain [up j, up i, dn i] ((sigmaL i i).map (whL [up j] [])) [up j, dn i, up i] := by
    simpa using (sChain_sigmaL i i).whisk [up j] []
  have ht : SChain [up j, dn i, up i]
      ((sigmaL i j).map (whL [] [up i]) ++ crossL [dn i] j i []) [dn i, up i, up j] :=
    (by simpa using (sChain_sigmaL i j).whisk [] [up i] :
      SChain [up j, dn i, up i] ((sigmaL i j).map (whL [] [up i])) [dn i, up j, up i]).append
      (by simp [crossL, Shape.dom, Shape.cod])
  rw [plcL_comp_of_mem μ [up j] [] (etaP_mem cs i _) (cl_mem_homPar (sChain_sigmaL i i) rfl),
    plcL_cl, Category.assoc]
  erw [cl_comp hs ht]
  rfl

theorem pcu_lhs8_h0 (i j : I) (μ : X) (hij : i ≠ j) (hd0 : D.d i j = 0) (hh : D.h i μ = 0) :
    plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫
      cl D Sc μ [up j, up i, dn i] [dn i, up i, up j] (lemma33_eq8_lhs i j i) =
    (-(zsign k (D.parity i) * (cs.c (wt D μ [up j]) i : k))) •
      cl D Sc μ [up j] [dn i, up i, up j] ((etaL i 0).map (whL [] [up j])) := by
  rw [pcu_lhs8_factor, eta_sigma_h0 cs i (wt D μ []) hh, map_smul, plcL_cl, Linear.smul_comp]
  have hc : SChain [up j] ((etaL i 0).map (whL [up j] [])) [up j, dn i, up i] := by
    simpa using (sChain_etaL i 0).whisk [up j] []
  have hs : SChain [up j, dn i, up i] ((sigmaL i j).map (whL [] [up i])) [dn i, up j, up i] := by
    simpa using (sChain_sigmaL i j).whisk [] [up i]
  have ht : SChain [dn i, up j, up i] (crossL [dn i] j i []) [dn i, up i, up j] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hc' : SChain [up j] [([], Shape.cup i, [up j])] [dn i, up i, up j] := by
    simp [Shape.dom, Shape.cod]
  have ht' : SChain [dn i, up i, up j] (crossL [dn i] i j []) [dn i, up j, up i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hq := congrArg (plcL D Sc μ [dn i] [] [up i, up j] [up i, up j])
    (cl_quadZero (Sc := Sc) i j (wt D μ []) hij hd0)
  simp only [map_smul, plcL_cl, cl_nil, plcL_id] at hq
  have E : cl D Sc μ [up j] [dn i, up i, up j]
      ((etaL i 0).map (whL [up j] []) ++ (sigmaL i j).map (whL [] [up i]) ++ crossL [dn i] j i []) =
      (Sc.t i j : k) • cl D Sc μ [up j] [dn i, up i, up j] ((etaL i 0).map (whL [] [up j])) := by
    rw [← cl_comp (hc.append hs) ht, show cl D Sc μ [up j] [dn i, up j, up i]
      ((etaL i 0).map (whL [up j] []) ++ (sigmaL i j).map (whL [] [up i])) =
      cl D Sc μ [up j] [dn i, up j, up i]
        [([], Shape.cup i, [up j]), ([dn i], Shape.cross i j, [])] from eq_2_4_b Sc i j μ]
    change (cl D Sc μ [up j] [dn i, up j, up i]
      ([([], Shape.cup i, [up j])] ++ crossL [dn i] i j [])) ≫ _ = _
    rw [← cl_comp hc' ht', Category.assoc, cl_comp ht' ht]
    erw [hq, Linear.comp_smul, Category.comp_id]
    rfl
  erw [cl_comp hc (hs.append ht)]
  simp only [← List.append_assoc]
  rw [E, smul_smul, c_wt_upj, Units.val_mul, wt_nil]
  congr 1
  ring

set_option maxHeartbeats 800000 in
theorem pcu_a_eq (i j : I) (μ : X) (hij : i ≠ j) (hh : D.h i μ = D.d i j) :
    pcuL cs i j μ ≫ pcuS i j μ ≫ pcuA i j μ =
      pcuR cs i j μ ≫ pcuS i j μ ≫ pcuA i j μ := by
  have hd := D.dn_cast hij
  have hv : D.h i (wt D μ [up j]) = 0 := by rw [h_wt_upj, hh, sub_self]
  rw [pcuL_a, pcuR_a cs i j μ hij, eta_sigma_h0 cs i _ hv, map_smul, plcL_cl]
  have E := congrArg (plcL D Sc μ [up j] [] [] [up i, dn i] (etaP cs i (wt D μ [])) ≫ ·)
    (lemma33_eq8_eq (Sc := Sc) i j μ hij)
  simp only [Preadditive.comp_sub, Preadditive.comp_add, Preadditive.comp_sum, Linear.comp_smul] at E
  rw [sum_eq_zero (fun p hp => sum_eq_zero (fun q _ => sum_eq_zero (fun s hs => by
    have hp := (mem_Ioo.1 hp).2
    have hs := mem_range.1 hs
    rw [pcu_term8_zero cs i j μ _ _ _ (by omega), smul_zero]))), add_zero] at E
  by_cases hd0 : D.d i j = 0
  · have hdn : D.dn i j = 0 := by omega
    rw [hdn, range_zero, sum_empty, sub_eq_zero] at E
    rw [← E, pcu_lhs8_h0 cs i j μ hij hd0 (by omega)]
    rfl
  · have hdpos : 0 < D.dn i j := by omega
    rw [pcu_lhs8_zero cs i j μ (by omega), zero_sub,
      sum_eq_single (D.dn i j - 1) (fun s hs hne => by
        have hs := mem_range.1 hs
        rw [pcu_term8_zero cs i j μ _ _ _ (by omega), smul_zero])
        (fun h => absurd (mem_range.2 (by omega)) h)] at E
    have er : D.dn i j - 1 - (D.dn i j - 1) = 0 := by omega
    rw [er, pcu_term8_top cs i j μ _ (by omega), smul_smul] at E
    have hp := parity_mul_dn D i j
    have hc : ((D.dn i j - 1 : ℕ) : ZMod 2) + 1 = (D.dn i j : ZMod 2) := by
      have h := congrArg (fun n : ℕ => (n : ZMod 2)) (show D.dn i j - 1 + 1 = D.dn i j by omega)
      simpa only [Nat.cast_add, Nat.cast_one] using h
    rw [← hc, mul_add, mul_one] at hp
    have hs : D.parity i * ((D.dn i j - 1 : ℕ) : ZMod 2) = D.parity i := by
      generalize D.parity i * ((D.dn i j - 1 : ℕ) : ZMod 2) = a at hp ⊢
      generalize D.parity i = b at hp ⊢
      revert a b
      decide
    rw [hs] at E
    rw [← neg_inj, E, neg_smul, neg_neg, c_wt_upj, Units.val_mul]
    congr 1
    ring

/-- **Brundan–Ellis, Lemma 7.1, (7.2).** The cup relation in its complete weight range. -/
theorem eq_7_2 (i j : I) (μ : X) (hij : i ≠ j) (hh : D.d i j ≤ D.h i μ) :
    pcuL cs i j μ = pcuR cs i j μ := by
  apply ext_EEF i j μ hij hh
  · rcases eq_or_lt_of_le hh with he | he
    · exact pcu_a_eq cs i j μ hij he.symm
    · exact pcu_a_gt cs i j μ hij he
  · exact pcu_b cs i j μ hij

end OddMath.SKM
