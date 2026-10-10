/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.CurlsR
import OddMath.SKM.Lemma33Rot

/-!
# Pitchfork relations for the leftward cups and caps (Brundan–Ellis, Lemma 6.1)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §6, Lemma 6.1
(TeX label `pitchforka`) and its proof, (6.3)–(6.5).

On `Eᵢ Fᵢ Eᵢ 1_λ` (rightmost region `λ = μ`, `h = ⟨hᵢ,λ⟩`):

* `leps`: `ε'` (at `λ + αᵢ`) on the two left strands of `Fᵢ Eᵢ Eᵢ`; `reps`: `ε'` (at `λ`) on the two
  right strands of `Eᵢ Fᵢ Eᵢ`;
* `L63`: the strand `Eᵢ` crossing the leftward cap `ε'` from the left (`σ` then `τ` then `ε'`);
* (6.3) (`eq_6_3`): for `h ≤ -1`, `-L63 = (↑ ⊗ ε') - δ_{h,-1} c_{λ;i}⁻¹ (ε ⊗ ↑)`, proved as in the
  paper by testing against the isomorphism (1.14) (`ext_EFE`): (6.4) (`check_6_4`, via (3.8), (5.17),
  (2.4), (3.1), (1.7)) and (6.5) (`check_6_5`, via (2.4), (3.1), (1.7), (5.18));
* (6.1) (`eq_6_1`): for `h ≤ -1`, the pitchfork relation for `ε'`, via (5.16), (5.18), (6.3) and
  (2.13).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Finset

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- `ε'` (at `λ + αᵢ`) on the two left strands of `Fᵢ Eᵢ Eᵢ 1_λ`. -/
def leps (i : I) (μ : X) :
    (pres D Sc).obj (ob D μ [dn i, up i, up i]) ⟶ (pres D Sc).obj (ob D μ [up i]) :=
  plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i (wt D μ [up i]))

/-- `ε'` (at `λ`) on the two right strands of `Eᵢ Fᵢ Eᵢ 1_λ`. -/
def reps (i : I) (μ : X) :
    (pres D Sc).obj (ob D μ [up i, dn i, up i]) ⟶ (pres D Sc).obj (ob D μ [up i]) :=
  plcL D Sc μ [up i] [] [dn i, up i] [] (epsP cs i (wt D μ []))

/-- The layers of the strand `Eᵢ` crossing the two strands `Fᵢ Eᵢ` to its right: `σ`, then `τ`. -/
def crossFE (i : I) : List (LayerData I) :=
  (sigmaL i i).map (whL [] [up i]) ++ [([dn i], Shape.cross i i, [])]

theorem sChain_crossFE (i : I) : SChain [up i, dn i, up i] (crossFE i) [dn i, up i, up i] :=
  (by simpa using (sChain_sigmaL i i).whisk [] [up i] :
    SChain [up i, dn i, up i] ((sigmaL i i).map (whL [] [up i])) [dn i, up i, up i]).append
    (by simp [Shape.dom, Shape.cod])

/-- The left-hand side of (6.3) (without the sign). -/
def L63 (i : I) (μ : X) :
    (pres D Sc).obj (ob D μ [up i, dn i, up i]) ⟶ (pres D Sc).obj (ob D μ [up i]) :=
  cl D Sc μ [up i, dn i, up i] [dn i, up i, up i] (crossFE i) ≫ leps cs i μ

/-! ## Testing against the isomorphism (1.14) -/

/-- `σ` on the two right strands of `Eᵢ Eᵢ Fᵢ`. -/
abbrev T1 (i : I) (μ : X) :
    (pres D Sc).obj (ob D μ [up i, up i, dn i]) ⟶ (pres D Sc).obj (ob D μ [up i, dn i, up i]) :=
  cl D Sc μ [up i, up i, dn i] [up i, dn i, up i] ((sigmaL i i).map (whL [up i] []))

/-- The rightward cup with `m` dots on its upward leg, to the right of `Eᵢ`. -/
abbrev T2 (i : I) (μ : X) (m : ℕ) :
    (pres D Sc).obj (ob D μ [up i]) ⟶ (pres D Sc).obj (ob D μ [up i, dn i, up i]) :=
  cl D Sc μ [up i] [up i, dn i, up i] ((etaL i m).map (whL [up i] []))

/-- Maps out of `Eᵢ Fᵢ Eᵢ 1_λ` with `⟨hᵢ,λ⟩ ≤ 0` are determined by their composites with `↑ ⊗ σ`
and with the dotted cups `↑ ⊗ ((1 ⊗ xᵐ) ∘ η)`, `m < -⟨hᵢ,λ⟩` (the isomorphism (1.14)). -/
theorem ext_EFE (i : I) (μ : X) (hh : D.h i μ ≤ 0) {Z : (pres D Sc).Presented}
    {f g : (pres D Sc).obj (ob D μ [up i, dn i, up i]) ⟶ Z}
    (h₁ : T1 i μ ≫ f = T1 i μ ≫ g)
    (h₂ : ∀ m : ℕ, (m : ℤ) < -D.h i μ → T2 i μ m ≫ f = T2 i μ m ≫ g) : f = g := by
  have E : -cl D Sc μ [up i, dn i, up i] [up i, dn i, up i]
        ((lcrossL i i ++ sigmaL i i).map (whL [up i] [])) +
      ∑ n ∈ range (-D.h i μ).toNat, cl D Sc μ [up i, dn i, up i] [up i, dn i, up i]
        ((dcapL i n ++ etaL i n).map (whL [up i] [])) =
      cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] [] := by
    have E0 := congrArg (plcL D Sc μ [up i] [] [dn i, up i] [dn i, up i])
      (cl_invM₁ Sc i (wt D μ []) hh)
    simp only [map_add, map_neg, map_sum, plcL_cl] at E0
    exact E0
  have hl : SChain [up i, dn i, up i] ((lcrossL i i).map (whL [up i] [])) [up i, up i, dn i] := by
    simpa using (sChain_lcrossL i i).whisk [up i] []
  have hs : SChain [up i, up i, dn i] ((sigmaL i i).map (whL [up i] [])) [up i, dn i, up i] := by
    simpa using (sChain_sigmaL i i).whisk [up i] []
  have hd : ∀ n, SChain [up i, dn i, up i] ((dcapL i n).map (whL [up i] [])) [up i] := fun n => by
    simpa using (sChain_dcapL i n).whisk [up i] []
  have he : ∀ n, SChain [up i] ((etaL i n).map (whL [up i] [])) [up i, dn i, up i] := fun n => by
    simpa using (sChain_etaL i n).whisk [up i] []
  have hid : 𝟙 ((pres D Sc).obj (ob D μ [up i, dn i, up i])) =
      -(cl D Sc μ [up i, dn i, up i] [up i, up i, dn i] ((lcrossL i i).map (whL [up i] [])) ≫ T1 i μ) +
      ∑ n ∈ range (-D.h i μ).toNat,
        cl D Sc μ [up i, dn i, up i] [up i] ((dcapL i n).map (whL [up i] [])) ≫ T2 i μ n := by
    rw [← cl_nil μ [up i, dn i, up i], ← E, cl_comp hl hs, List.map_append]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [cl_comp (hd n) (he n), List.map_append]
  rw [← Category.id_comp f, ← Category.id_comp g, hid]
  simp only [Preadditive.add_comp, Preadditive.neg_comp, Preadditive.sum_comp, Category.assoc, h₁]
  congr 1
  refine sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  rw [h₂ n (by omega)]


/-! ## (6.4) -/

theorem c_wt_up (i : I) (μ : X) : cs.c (wt D μ [up i]) i = cs.c μ i := by
  have := cs.shift μ i i
  rw [Sc.t_self, one_mul] at this
  simpa [wt, sh, add_comm] using this

/-- The crossing on the two upward strands of `Eᵢ Eᵢ Fᵢ`. -/
abbrev tauEEF (i : I) : List (LayerData I) := [([], Shape.cross i i, [dn i])]

theorem sChain_tauEEF (i : I) : SChain [up i, up i, dn i] (tauEEF i) [up i, up i, dn i] := by
  simp [Shape.dom, Shape.cod]

/-- `τ`, then `σ` on the two right strands, then `ε` with `m` dots on the two left strands, moved
into the form `τ`, dots, `τ`, `ε` on the right ((2.4)). -/
theorem tau_sigma_epsL (i : I) (μ : X) (m : ℕ) :
    cl D Sc μ [up i, up i, dn i] [up i]
        (tauEEF i ++ (sigmaL i i).map (whL [up i] []) ++ (epsL i m).map (whL [] [up i])) =
      zsign k (D.parity i * (m : ZMod 2)) •
        cl D Sc μ [up i, up i, dn i] [up i]
          (tauEEF i ++ dotsL [] i [up i, dn i] m ++ tauEEF i ++ [([up i], Shape.cap i, [])]) := by
  -- the dots move below `σ`
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := [up i, up i, dn i]) (T := [up i])
    (tauEEF i) [([], Shape.cap i, [up i])] (s := [up i]) (s' := [up i]) (t := [up i, dn i])
    (t' := [dn i, up i]) (A := dotsL [] i [] m) (B := sigmaL i i) (sChain_dotsL [] i [] m)
    (sChain_sigmaL i i)
  have hdm : (dotsL [] i [] m).map (whL [] [up i, dn i]) = dotsL [] i [up i, dn i] m := by
    simp [dotsL, whL]
  rw [parsum_dotsL, parsum_sigmaL, hdm] at E
  have E' := congrArg (zsign k ((m : ZMod 2) * D.parity i * (D.parity i * D.parity i)) • ·) E
  simp only [smul_smul, zsign_mul_self', one_smul] at E'
  have e1 : tauEEF i ++ (sigmaL i i).map (whL [up i] []) ++ (epsL i m).map (whL [] [up i]) =
      tauEEF i ++ (sigmaL i i).map (whL [up i] []) ++ (dotsL [] i [] m).map (whL [] [dn i, up i]) ++
        [([], Shape.cap i, [up i])] := by
    simp [epsL, dotsL, whL]
  have e2 : tauEEF i ++ dotsL [] i [up i, dn i] m ++
      (sigmaL i i).map (whL [up i] []) ++ [([], Shape.cap i, [up i])] =
      (tauEEF i ++ dotsL [] i [up i, dn i] m) ++
        ((sigmaL i i).map (whL [up i] []) ++ [([], Shape.cap i, [up i])]).map (whL [] []) ++ [] := by
    simp
  -- (2.4) in context
  have E2 := cl_step (D := D) (Sc := Sc) μ (s₀ := [up i, up i, dn i]) (t₀ := [up i])
    (tauEEF i ++ dotsL [] i [up i, dn i] m) [] [] [] (eq_2_4_a Sc i i μ)
    (L := (tauEEF i ++ dotsL [] i [up i, dn i] m) ++
        ((sigmaL i i).map (whL [up i] []) ++ [([], Shape.cap i, [up i])]).map (whL [] []) ++ [])
    (L' := tauEEF i ++ dotsL [] i [up i, dn i] m ++ tauEEF i ++ [([up i], Shape.cap i, [])])
    ((sChain_tauEEF i).append (sChain_dotsL [] i [up i, dn i] m))
    rfl rfl (by simp)
  rw [e1, ← E', e2, E2]
  congr 1
  congr 1
  generalize D.parity i = a; generalize (m : ZMod 2) = x; revert a x; decide


/-- A diagram on the two upward strands of `Eᵢ Eᵢ Fᵢ` between the crossing below and the cap `ε` on
the right above. -/
theorem ctx_tau_capR (i : I) (μ : X) {L : List (LayerData I)} (hL : SChain [up i, up i] L [up i, up i]) :
    cl D Sc μ [up i, up i, dn i] [up i] (tauEEF i ++ L.map (whL [] [dn i]) ++ [([up i], Shape.cap i, [])]) =
      cl D Sc μ [up i, up i, dn i] [up i, up i, dn i] (tauEEF i) ≫
        plcL D Sc μ [] [dn i] [up i, up i] [up i, up i] (cl D Sc (wt D μ [dn i]) [up i, up i] [up i, up i] L) ≫
          cl D Sc μ [up i, up i, dn i] [up i] [([up i], Shape.cap i, [])] := by
  have h0 : SChain [up i, up i, dn i] [([up i], Shape.cap i, [])] [up i] := by
    simp [Shape.dom, Shape.cod]
  rw [plcL_cl]
  change _ = cl D Sc μ [up i, up i, dn i] [up i, up i, dn i] (tauEEF i) ≫
    cl D Sc μ [up i, up i, dn i] [up i, up i, dn i] (L.map (whL [] [dn i])) ≫ _
  have hLd : SChain [up i, up i, dn i] (L.map (whL [] [dn i])) [up i, up i, dn i] := by
    simpa using hL.whisk [] [dn i]
  rw [cl_comp hLd h0, cl_comp (sChain_tauEEF i) (hLd.append h0), List.append_assoc]

/-- `τ`, `m` dots on the left strand, `τ`, `ε` on the right: by (3.1) and `τ² = 0`. -/
theorem tau_dots_tau (i : I) (μ : X) (m : ℕ) :
    cl D Sc μ [up i, up i, dn i] [up i]
        (tauEEF i ++ dotsL [] i [up i, dn i] m ++ tauEEF i ++ [([up i], Shape.cap i, [])]) =
      ∑ s ∈ range m, zsign k (D.parity i * (s : ZMod 2)) •
        cl D Sc μ [up i, up i, dn i] [up i]
          (tauEEF i ++ dotsL [] i [up i, dn i] (m - 1 - s) ++ dotsL [up i] i [dn i] s ++
            [([up i], Shape.cap i, [])]) := by
  have hT : SChain [up i, up i] (crossL [] i i []) [up i, up i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have L1 := lemma31_eq1_eq Sc i (wt D μ [dn i]) m
  rw [sub_eq_iff_eq_add] at L1
  have e1 : tauEEF i ++ dotsL [] i [up i, dn i] m ++ tauEEF i ++ [([up i], Shape.cap i, [])] =
      tauEEF i ++ (dotsL [] i [up i] m ++ crossL [] i i []).map (whL [] [dn i]) ++
        [([up i], Shape.cap i, [])] := by
    simp [dotsL, crossL, whL]
  have hz : cl D Sc μ [up i, up i, dn i] [up i, up i, dn i] (tauEEF i) ≫
      plcL D Sc μ [] [dn i] [up i, up i] [up i, up i]
        (cl D Sc (wt D μ [dn i]) [up i, up i] [up i, up i] (crossL [] i i [] ++ dotsL [up i] i [] m)) = 0 := by
    have e : cl D Sc μ [up i, up i, dn i] [up i, up i, dn i] (tauEEF i) =
        plcL D Sc μ [] [dn i] [up i, up i] [up i, up i]
          (cl D Sc (wt D μ [dn i]) [up i, up i] [up i, up i] (crossL [] i i [])) := by
      rw [plcL_cl]; rfl
    have hd : SChain [up i, up i] (dotsL [up i] i [] m) [up i, up i] := sChain_dotsL [up i] i [] m
    rw [e, ← plcL_cl_comp μ [] [dn i] _ _ hT (hT.append hd), cl_comp hT (hT.append hd),
      ← List.append_assoc, ← cl_comp (hT.append hT) hd, cl_quadEq, Limits.zero_comp, map_zero]
  rw [e1, ctx_tau_capR i μ ((sChain_dotsL [] i [up i] m).append hT), L1, map_add, map_sum,
    map_smul, Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul]
  simp only [← Category.assoc]
  rw [hz, Limits.zero_comp, smul_zero, add_zero, Preadditive.comp_sum, Preadditive.sum_comp]
  refine sum_congr rfl fun s _ => ?_
  rw [map_smul, Linear.comp_smul, Linear.smul_comp, Category.assoc,
    ← ctx_tau_capR i μ ((sChain_dotsL [] i [up i] _).append (sChain_dotsL [up i] i [] s))]
  congr 2
  simp [dotsL, whL]


theorem lbub_id (i : I) (μ : X) : lbub i μ (𝟙 ((pres D Sc).obj (ob D (wt D μ [up i]) []))) = 𝟙 _ := by
  rw [lbub, ← cl_nil (wt D μ [up i]) [], plcL_cl]
  exact cl_nil μ [up i]

/-- `σ` on the two left strands of `Eᵢ Fᵢ Eᵢ` followed by `ε'`: by (5.17) at `λ + αᵢ`. -/
theorem sigma_leps (i : I) (μ : X) :
    cl D Sc μ [up i, dn i, up i] [dn i, up i, up i] ((sigmaL i i).map (whL [] [up i])) ≫ leps cs i μ =
      ∑ m ∈ range ((D.h i (wt D μ [up i])).toNat + 1), zsign k (D.parity i * (m : ZMod 2)) •
        (cl D Sc μ [up i, dn i, up i] [up i] ((epsL i m).map (whL [] [up i])) ≫
          lbub i μ (bubR cs i (wt D μ [up i]) (-(m : ℤ) - 1))) := by
  have e : cl D Sc μ [up i, dn i, up i] [dn i, up i, up i] ((sigmaL i i).map (whL [] [up i])) =
      plcL D Sc μ [] [up i] [up i, dn i] [dn i, up i]
        (cl D Sc (wt D μ [up i]) [up i, dn i] [dn i, up i] (sigmaL i i)) := by
    rw [plcL_cl]; rfl
  rw [e, leps, ← plcL_comp_of_mem μ [] [up i] (sigma_mem i _) (epsP_mem cs i _), eq_5_17_a, map_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [map_smul, plcL_comp_of_mem μ [] [up i] (epsL_mem i _ m) (bubR_mem cs i _ _), plcL_cl]
  rfl

/-- The scalar `δ_{⟨hᵢ,λ⟩,-1} c_{λ;i}⁻¹`. -/
def dsc (i : I) (μ : X) : k := if D.h i μ = -1 then (↑(cs.c μ i)⁻¹ : k) else 0

/-- **(6.4)**: the composite of (6.3) with `↑ ⊗ σ` (for `⟨hᵢ,λ⟩ ≤ -1`). -/
theorem check_6_4 (i : I) (μ : X) (hh : D.h i μ ≤ -1) :
    T1 i μ ≫ (-(L63 cs i μ)) = T1 i μ ≫ (reps cs i μ - dsc cs i μ •
        cl D Sc μ [up i, dn i, up i] [up i] [([], Shape.cap i, [up i])]) := by
  have hs : SChain [up i, up i, dn i] ((sigmaL i i).map (whL [up i] [])) [up i, dn i, up i] := by
    simpa using (sChain_sigmaL i i).whisk [up i] []
  -- the right-hand side
  have hR1 : T1 i μ ≫ reps cs i μ = 0 := by
    have e : T1 i μ = plcL D Sc μ [up i] [] [up i, dn i] [dn i, up i]
        (cl D Sc (wt D μ []) [up i, dn i] [dn i, up i] (sigmaL i i)) := by
      rw [plcL_cl]; rfl
    rw [e, reps, ← plcL_comp_of_mem μ [up i] [] (sigma_mem i _) (epsP_mem cs i _),
      eq_2_14_a cs i _ (by simp only [wt_nil]; omega), map_zero]
  have hR2 : T1 i μ ≫ cl D Sc μ [up i, dn i, up i] [up i] [([], Shape.cap i, [up i])] =
      cl D Sc μ [up i, up i, dn i] [up i] (tauEEF i ++ [([up i], Shape.cap i, [])]) := by
    rw [cl_comp hs (by simp [Shape.dom, Shape.cod]), eq_2_4_a]
    rfl
  -- the left-hand side
  have hL : T1 i μ ≫ L63 cs i μ =
      ∑ m ∈ range ((D.h i (wt D μ [up i])).toNat + 1), zsign k (D.parity i * (m : ZMod 2)) •
        (cl D Sc μ [up i, up i, dn i] [up i]
            (tauEEF i ++ (sigmaL i i).map (whL [up i] []) ++ (epsL i m).map (whL [] [up i])) ≫
          lbub i μ (bubR cs i (wt D μ [up i]) (-(m : ℤ) - 1))) := by
    have E8 := lemma33_eq8 Sc i i i μ (by simp)
    have e1 : (sigmaL i i).map (whL [up i] []) ++ crossFE i = lemma33_eq8_lhs i i i := by
      simp [lemma33_eq8_lhs, crossFE, crossL]
    have e2 : lemma33_eq8_rhs i i i = (tauEEF i ++ (sigmaL i i).map (whL [up i] [])) ++
        (sigmaL i i).map (whL [] [up i]) := by
      simp [lemma33_eq8_rhs, crossL]
    have h3 : SChain [up i, up i, dn i] (tauEEF i ++ (sigmaL i i).map (whL [up i] [])) [up i, dn i, up i] :=
      (sChain_tauEEF i).append hs
    have h4 : SChain [up i, dn i, up i] ((sigmaL i i).map (whL [] [up i])) [dn i, up i, up i] := by
      simpa using (sChain_sigmaL i i).whisk [] [up i]
    rw [L63, ← Category.assoc, cl_comp hs (sChain_crossFE i), e1, E8, e2, ← cl_comp h3 h4,
      Category.assoc, sigma_leps, Preadditive.comp_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [Linear.comp_smul, ← Category.assoc, cl_comp h3 (by simpa using (sChain_epsL i m).whisk [] [up i])]
  rw [Preadditive.comp_sub, Linear.comp_smul, hR1, hR2, zero_sub, Preadditive.comp_neg, hL]
  congr 1
  rcases eq_or_lt_of_le hh with h1 | h1
  · -- `⟨hᵢ,λ⟩ = -1`
    have hν : D.h i (wt D μ [up i]) = 1 := by rw [h_wt_up]; omega
    rw [hν, dsc, ite_eq_left h1, show (1 : ℤ).toNat + 1 = 2 from rfl, sum_range_succ, sum_range_one]
    rw [tau_sigma_epsL, tau_sigma_epsL, tau_dots_tau, tau_dots_tau, sum_range_zero, smul_zero,
      Limits.zero_comp, smul_zero, zero_add, sum_range_one]
    have hb : bubR cs i (wt D μ [up i]) (-((1 : ℕ) : ℤ) - 1) = (↑(cs.c μ i)⁻¹ : k) • 𝟙 _ := by
      rw [show -((1 : ℕ) : ℤ) - 1 = -D.h i (wt D μ [up i]) - 1 by rw [hν]; norm_num, bubR_eq_c,
        c_wt_up]
    have hl : lbub i μ ((↑(cs.c μ i)⁻¹ : k) • 𝟙 ((pres D Sc).obj (ob D (wt D μ [up i]) []))) =
        (↑(cs.c μ i)⁻¹ : k) • 𝟙 _ := by
      rw [lbub, map_smul, ← lbub, lbub_id]
    rw [hb, hl, Linear.comp_smul, Category.comp_id, smul_smul, smul_smul, smul_smul]
    simp only [dotsL, List.replicate_zero, List.append_nil, Nat.cast_zero, mul_zero, zsign_zero,
      mul_one, Nat.cast_one, show 1 - 1 - 0 = 0 from rfl]
    congr 1
    rw [mul_comm, ← mul_assoc, zsign_mul_self', one_mul]
  · have hν : (D.h i (wt D μ [up i])).toNat = 0 := by rw [h_wt_up]; omega
    rw [hν, dsc, ite_eq_right (by omega), zero_smul, zero_add, sum_range_one, tau_sigma_epsL,
      tau_dots_tau, sum_range_zero, smul_zero, Limits.zero_comp, smul_zero]


/-! ## (6.5) -/

/-- The left curl with `n` dots on the loop before the crossing (the left-hand side of (5.18)). -/
abbrev curl18 (i : I) (μ : X) (n : ℕ) :
    (pres D Sc).obj (ob D μ [up i]) ⟶ (pres D Sc).obj (ob D μ [up i]) :=
  cl D Sc μ [up i] [dn i, up i, up i]
    ([([], Shape.cup i, [up i])] ++ dotsL [dn i] i [up i] n ++ [([dn i], Shape.cross i i, [])]) ≫
    leps cs i μ

theorem curl18_eq_zero (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) + D.h i μ + 3 ≤ 0) :
    curl18 cs i μ n = 0 := by
  rw [curl18, leps, eq_5_18, show ((n : ℤ) + D.h i μ + 3).toNat = 0 by omega, sum_range_zero]

theorem curl18_eq_c (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) + D.h i μ + 3 = 1) :
    curl18 cs i μ n = (↑(cs.c μ i)⁻¹ : k) • 𝟙 _ := by
  rw [curl18, leps, eq_5_18, show ((n : ℤ) + D.h i μ + 3).toNat = 1 by omega, sum_range_one,
    Nat.cast_zero, mul_zero, zsign_zero, one_smul,
    show (n : ℤ) - ((0 : ℕ) : ℤ) - 1 = -D.h i (wt D μ [up i]) - 1 by rw [h_wt_up]; omega,
    bubR_eq_c, c_wt_up, lbub, map_smul, ← lbub, lbub_id, dotsL, List.replicate_zero, cl_nil,
    Linear.smul_comp, Category.id_comp]

theorem rbub_id (i : I) (μ : X) : rbub i μ (𝟙 ((pres D Sc).obj (ob D (wt D μ []) []))) = 𝟙 _ := by
  rw [rbub, ← cl_nil (wt D μ []) [], plcL_cl]
  exact cl_nil μ [up i]


/-- `T2 m ≫ L63`: the strand crossing a clockwise dotted bubble, expanded into dots below dotted
left curls ((2.4) and (3.1)). -/
theorem T2_L63 (i : I) (μ : X) (m : ℕ) :
    T2 i μ m ≫ L63 cs i μ =
      -∑ s ∈ range m, zsign k (D.parity i * (m - 1 - s : ℕ) * (D.parity i * s) + D.parity i * s) •
        (cl D Sc μ [up i] [up i] (dotsL [] i [] s) ≫ curl18 cs i μ (m - 1 - s)) := by
  have hT : SChain [up i, up i] (crossL [] i i []) [up i, up i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have he : SChain [up i] ((etaL i m).map (whL [up i] [])) [up i, dn i, up i] := by
    simpa using (sChain_etaL i m).whisk [up i] []
  -- the dots move above `σ`
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := [up i]) (T := [dn i, up i, up i])
    [([up i], Shape.cup i, [])] [([dn i], Shape.cross i i, [])] (s := [up i, dn i]) (s' := [dn i, up i])
    (t := [up i]) (t' := [up i]) (A := sigmaL i i) (B := dotsL [] i [] m) (sChain_sigmaL i i)
    (sChain_dotsL [] i [] m)
  rw [parsum_sigmaL, parsum_dotsL] at E
  have E' := congrArg (zsign k (D.parity i * D.parity i * ((m : ZMod 2) * D.parity i)) • ·) E
  simp only [smul_smul, zsign_mul_self', one_smul] at E'
  have e1 : (etaL i m).map (whL [up i] []) ++ crossFE i =
      [([up i], Shape.cup i, [])] ++ (dotsL [] i [] m).map (whL [up i, dn i] []) ++
        (sigmaL i i).map (whL [] [up i]) ++ [([dn i], Shape.cross i i, [])] := by
    simp [etaL, crossFE, dotsL, whL]
  -- (2.4)
  have hdd : SChain [dn i, up i, up i] ((dotsL [] i [] m).map (whL [dn i, up i] []))
      [dn i, up i, up i] := by simpa using (sChain_dotsL [] i [] m).whisk [dn i, up i] []
  have hcr : SChain [dn i, up i, up i] [([dn i], Shape.cross i i, [])] [dn i, up i, up i] := by
    simp [Shape.dom, Shape.cod]
  have E2 := cl_step (D := D) (Sc := Sc) μ (s₀ := [up i]) (t₀ := [dn i, up i, up i])
    [] ((dotsL [] i [] m).map (whL [dn i, up i] []) ++ [([dn i], Shape.cross i i, [])]) [] []
    (eq_2_4_b Sc i i μ)
    (L := [([up i], Shape.cup i, [])] ++ (sigmaL i i).map (whL [] [up i]) ++
      (dotsL [] i [] m).map (whL [dn i, up i] []) ++ [([dn i], Shape.cross i i, [])])
    (L' := [([], Shape.cup i, [up i])] ++ (crossL [] i i [] ++ dotsL [up i] i [] m ++
      crossL [] i i []).map (whL [dn i] []))
    rfl (hdd.append hcr) (by simp) (by simp [crossL, dotsL, whL])
  have L1 := lemma31_eq1_eq Sc i (wt D μ []) m
  have L1' : cl D Sc (wt D μ []) [up i, up i] [up i, up i]
      (crossL [] i i [] ++ dotsL [up i] i [] m ++ crossL [] i i []) =
      -(zsign k (D.parity i * D.parity i * m) • ∑ s ∈ range m, zsign k (D.parity i * s) •
        cl D Sc (wt D μ []) [up i, up i] [up i, up i]
          (dotsL [] i [up i] (m - 1 - s) ++ dotsL [up i] i [] s ++ crossL [] i i [])) := by
    have hd : SChain [up i, up i] (dotsL [up i] i [] m) [up i, up i] := sChain_dotsL [up i] i [] m
    have hdl : SChain [up i, up i] (dotsL [] i [up i] m) [up i, up i] := sChain_dotsL [] i [up i] m
    have L1'' : cl D Sc (wt D μ []) [up i, up i] [up i, up i] (crossL [] i i [] ++ dotsL [up i] i [] m) =
        zsign k (D.parity i * D.parity i * m) •
          (cl D Sc (wt D μ []) [up i, up i] [up i, up i] (dotsL [] i [up i] m ++ crossL [] i i []) -
            ∑ s ∈ range m, zsign k (D.parity i * s) • cl D Sc (wt D μ []) [up i, up i] [up i, up i]
              (dotsL [] i [up i] (m - 1 - s) ++ dotsL [up i] i [] s)) := by
      rw [← L1, sub_sub_cancel, smul_smul, zsign_mul_self', one_smul]
    rw [← cl_comp (hT.append hd) hT, L1'', Linear.smul_comp, Preadditive.sub_comp,
      Preadditive.sum_comp, cl_comp (hdl.append hT) hT, List.append_assoc,
      ← cl_comp hdl (hT.append hT), cl_quadEq, Limits.comp_zero, zero_sub, smul_neg]
    congr 2
    refine sum_congr rfl fun s _ => ?_
    have hds : SChain [up i, up i] (dotsL [] i [up i] (m - 1 - s) ++ dotsL [up i] i [] s)
        [up i, up i] := (sChain_dotsL [] i [up i] _).append (sChain_dotsL [up i] i [] s)
    rw [Linear.smul_comp, cl_comp hds hT]
  have hX : SChain [up i, up i] (crossL [] i i [] ++ dotsL [up i] i [] m ++ crossL [] i i [])
      [up i, up i] := (hT.append (sChain_dotsL [up i] i [] m)).append hT
  rw [L63, ← Category.assoc, cl_comp he (sChain_crossFE i), e1, ← E', Linear.smul_comp, E2,
    cup_plc_up2 i μ hX, L1', map_neg, map_smul, map_sum, Preadditive.comp_neg,
    Preadditive.neg_comp, Linear.comp_smul, Linear.smul_comp, Preadditive.comp_sum,
    Preadditive.sum_comp, smul_neg, smul_smul, smul_sum]
  congr 1
  refine sum_congr rfl fun s hs => ?_
  rw [mem_range] at hs
  set n := m - 1 - s with hn
  have hdl : SChain [up i] (dotsL [] i [] n) [up i] := sChain_dotsL [] i [] n
  have hdr : SChain [up i] (dotsL [] i [] s) [up i] := sChain_dotsL [] i [] s
  have Ei := cl_interchange (D := D) (Sc := Sc) (μ := wt D μ []) (S := [up i, up i]) (T := [up i, up i])
    [] (crossL [] i i []) hdl hdr
  rw [parsum_dotsL, parsum_dotsL] at Ei
  have e2 : ∀ (a b : List (Letter I)) (r : ℕ), (dotsL [] i [] r).map (whL a b) = dotsL a i b r := by
    intro a b r; simp [dotsL, whL]
  simp only [e2, List.nil_append] at Ei
  rw [map_smul, Ei, map_smul]
  simp only [Linear.comp_smul, Linear.smul_comp, smul_smul]
  have hY : SChain [up i, up i] (dotsL [up i] i [] s ++ dotsL [] i [up i] n ++ crossL [] i i [])
      [up i, up i] := ((sChain_dotsL [up i] i [] s).append (sChain_dotsL [] i [up i] n)).append hT
  rw [← cup_plc_up2 i μ hY]
  have e3 : [([], Shape.cup i, [up i])] ++ (dotsL [up i] i [] s ++ dotsL [] i [up i] n ++
      crossL [] i i []).map (whL [dn i] []) = [([], Shape.cup i, [up i])] ++ dotsL [dn i, up i] i [] s ++
        (dotsL [dn i] i [up i] n ++ [([dn i], Shape.cross i i, [])]) := by
    simp [dotsL, crossL, whL]
  have hZ : SChain [up i] ([([], Shape.cup i, [up i])] ++ dotsL [dn i] i [up i] n ++
      [([dn i], Shape.cross i i, [])]) [dn i, up i, up i] := by
    refine ((show SChain [up i] [([], Shape.cup i, [up i])] [dn i, up i, up i] by
      simp [Shape.dom, Shape.cod]).append (sChain_dotsL [dn i] i [up i] n)).append ?_
    simp [Shape.dom, Shape.cod]
  rw [e3, cup_dotsR, List.append_assoc, ← List.append_assoc [([], Shape.cup i, [up i])],
    ← cl_comp hdr hZ, Category.assoc]
  congr 1
  simp only [← zsign_add]
  congr 1
  generalize D.parity i = a; generalize (n : ZMod 2) = x; generalize (s : ZMod 2) = y
  generalize (m : ZMod 2) = z
  revert a x y z; decide


/-- **(6.5)**: the composite of (6.3) with the dotted cups `↑ ⊗ ((1 ⊗ xᵐ) ∘ η)`, `m < -⟨hᵢ,λ⟩`
(for `⟨hᵢ,λ⟩ ≤ -1`). -/
theorem check_6_5 (i : I) (μ : X) (hh : D.h i μ ≤ -1) (m : ℕ) (hm : (m : ℤ) < -D.h i μ) :
    T2 i μ m ≫ (-(L63 cs i μ)) = T2 i μ m ≫ (reps cs i μ - dsc cs i μ •
        cl D Sc μ [up i, dn i, up i] [up i] [([], Shape.cap i, [up i])]) := by
  have eT2 : T2 i μ m = plcL D Sc μ [up i] [] [] [dn i, up i]
      (cl D Sc (wt D μ []) [] [dn i, up i] (etaL i m)) := by
    rw [plcL_cl]; rfl
  have hR1 : T2 i μ m ≫ reps cs i μ = rbub i μ (bubR cs i (wt D μ []) m) := by
    rw [eT2, reps, ← plcL_comp_of_mem μ [up i] [] (etaL_mem i _ m) (epsP_mem cs i _), ← bubR_nat]
    rfl
  have hR2 : T2 i μ m ≫ cl D Sc μ [up i, dn i, up i] [up i] [([], Shape.cap i, [up i])] =
      cl D Sc μ [up i] [up i] (dotsL [] i [] m) := by
    rw [eT2]; exact etaL_capR i μ m
  rw [Preadditive.comp_neg, T2_L63, neg_neg, Preadditive.comp_sub, Linear.comp_smul, hR1, hR2,
    bubR_nat, ← bubR_nat]
  have hb : bubR cs i (wt D μ []) (m : ℤ) =
      if (m : ℤ) = -D.h i μ - 1 then (↑(cs.c μ i)⁻¹ : k) • 𝟙 _ else 0 := by
    rw [bubR_nat]; exact eq_2_14_c cs i (wt D μ []) m hm
  rw [hb]
  rcases eq_or_lt_of_le hh with h1 | h1
  · -- `⟨hᵢ,λ⟩ = -1`, so `m = 0`
    obtain rfl : m = 0 := by omega
    rw [sum_range_zero, ite_eq_left (show ((0 : ℕ) : ℤ) = -D.h i μ - 1 by omega), dsc,
      ite_eq_left h1, rbub, map_smul, ← rbub,
      rbub_id, dotsL, List.replicate_zero, cl_nil, sub_self]
  · rw [dsc, ite_eq_right (show ¬ D.h i μ = -1 by omega), zero_smul, sub_zero]
    by_cases hm' : (m : ℤ) = -D.h i μ - 1
    · rw [ite_eq_left hm', rbub, map_smul, ← rbub, rbub_id, sum_eq_single 0]
      · rw [curl18_eq_c cs i μ _ (by omega), dotsL, List.replicate_zero, cl_nil, Category.id_comp]
        simp [zsign_zero]
      · intro s hs hs0
        rw [mem_range] at hs
        rw [curl18_eq_zero cs i μ _ (by omega), Limits.comp_zero, smul_zero]
      · intro h0; exfalso; exact h0 (mem_range.2 (by omega))
    · rw [ite_eq_right hm', rbub, map_zero]
      refine sum_eq_zero fun s hs => ?_
      rw [mem_range] at hs
      rw [curl18_eq_zero cs i μ _ (by omega), Limits.comp_zero, smul_zero]

/-- **Brundan–Ellis, (6.3)** (the claim in the proof of Lemma 6.1): for `⟨hᵢ,λ⟩ ≤ -1`, minus the
strand `Eᵢ` crossing the leftward cap `ε'` from the left equals `↑ ⊗ ε'` minus
`δ_{⟨hᵢ,λ⟩,-1} c_{λ;i}⁻¹` times the rightward cap `ε` on the left of `↑`. -/
theorem eq_6_3 (i : I) (μ : X) (hh : D.h i μ ≤ -1) :
    -(L63 cs i μ) = reps cs i μ - dsc cs i μ •
      cl D Sc μ [up i, dn i, up i] [up i] [([], Shape.cap i, [up i])] :=
  ext_EFE i μ (by omega) (check_6_4 cs i μ hh) fun m hm => check_6_5 cs i μ hh m hm


/-! ## (6.1) -/

theorem dcapRHS_mem (i : I) (μ : X) (n : ℕ) :
    dcapRHS cs i μ n ∈ homPar D Sc μ [dn i, up i] [] (D.parity i * (n : ZMod 2)) := by
  refine Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ ?_
  have h := comp_mem_homPar (cl_mem_homPar (D := D) (Sc := Sc) (μ := μ) (sChain_dR i r) rfl)
    (comp_mem_homPar (epsP_mem cs i μ) (bubL_mem cs i μ (-(n : ℤ) - r - 2)))
  convert h using 2
  rw [parsum_dotsL, ipar]
  push_cast
  generalize D.parity i = a; generalize (n : ZMod 2) = x; generalize (r : ZMod 2) = y
  generalize (D.h i μ : ZMod 2) = z
  revert a x y z; decide

/-- **Brundan–Ellis, Lemma 6.1, (6.1)**: for `⟨hᵢ,λ⟩ ≤ -1`, on `Fᵢ Eᵢ Eᵢ 1_λ`, the upward crossing
on the two upward strands followed by `ε'` on the left equals the leftward crossing on the two left
strands followed by `ε'` on the right. -/
theorem eq_6_1 (i : I) (μ : X) (hh : D.h i μ ≤ -1) :
    cl D Sc μ [dn i, up i, up i] [dn i, up i, up i] [([dn i], Shape.cross i i, [])] ≫ leps cs i μ =
      cl D Sc μ [dn i, up i, up i] [up i, dn i, up i] [([], Shape.lcross i i, [up i])] ≫
        reps cs i μ := by
  set ν := wt D μ [up i] with hν
  have hνh : D.h i ν = D.h i μ + 2 := h_wt_up i μ
  have hc : SChain [dn i, up i, up i] [([dn i], Shape.cross i i, [])] [dn i, up i, up i] := by
    simp [Shape.dom, Shape.cod]
  have hl : SChain [dn i, up i, up i] [([], Shape.lcross i i, [up i])] [up i, dn i, up i] := by
    simp [Shape.dom, Shape.cod]
  -- the claim: `lcross ≫ L63 = -(τ ≫ leps)`
  have claim : cl D Sc μ [dn i, up i, up i] [up i, dn i, up i] [([], Shape.lcross i i, [up i])] ≫
      L63 cs i μ = -(cl D Sc μ [dn i, up i, up i] [dn i, up i, up i] [([dn i], Shape.cross i i, [])] ≫
        leps cs i μ) := by
    have E16 := congrArg (plcL D Sc μ [] [up i] [dn i, up i] [dn i, up i]) (eq_5_16 cs i ν)
    have e1 : cl D Sc μ [dn i, up i, up i] [up i, dn i, up i] [([], Shape.lcross i i, [up i])] ≫
        cl D Sc μ [up i, dn i, up i] [dn i, up i, up i] (crossFE i) =
        plcL D Sc μ [] [up i] [dn i, up i] [dn i, up i]
          (cl D Sc ν [dn i, up i] [dn i, up i] (lcrossL i i ++ sigmaL i i)) ≫
            cl D Sc μ [dn i, up i, up i] [dn i, up i, up i] [([dn i], Shape.cross i i, [])] := by
      rw [plcL_cl]
      change _ = cl D Sc μ [dn i, up i, up i] [dn i, up i, up i]
        ((lcrossL i i ++ sigmaL i i).map (whL [] [up i])) ≫ _
      have hls : SChain [dn i, up i, up i] ((lcrossL i i ++ sigmaL i i).map (whL [] [up i]))
          [dn i, up i, up i] := by
        simpa using ((sChain_lcrossL i i).append (sChain_sigmaL i i)).whisk [] [up i]
      rw [cl_comp hl (sChain_crossFE i), cl_comp hls hc]
      simp [crossFE, lcrossL, whL]
    rw [L63, ← Category.assoc, e1, E16, map_sub, map_sum, plcL_cl, Preadditive.sub_comp,
      Preadditive.sub_comp, Preadditive.sum_comp, Preadditive.sum_comp]
    have hz : ∀ n ∈ range (-D.h i ν).toNat,
        (plcL D Sc μ [] [up i] [dn i, up i] [dn i, up i]
          (dcapRHS cs i ν n ≫ cl D Sc ν [] [dn i, up i] (etaL i n)) ≫
          cl D Sc μ [dn i, up i, up i] [dn i, up i, up i] [([dn i], Shape.cross i i, [])]) ≫
          leps cs i μ = 0 := by
      intro n hn
      rw [mem_range] at hn
      have he : plcL D Sc μ [] [up i] [] [dn i, up i] (cl D Sc ν [] [dn i, up i] (etaL i n)) ≫
          cl D Sc μ [dn i, up i, up i] [dn i, up i, up i] [([dn i], Shape.cross i i, [])] =
          cl D Sc μ [up i] [dn i, up i, up i]
            ([([], Shape.cup i, [up i])] ++ dotsL [dn i] i [up i] n ++ [([dn i], Shape.cross i i, [])]) := by
        rw [plcL_cl]
        change cl D Sc μ [up i] [dn i, up i, up i] ((etaL i n).map (whL [] [up i])) ≫ _ = _
        rw [cl_comp (by simpa using (sChain_etaL i n).whisk [] [up i]) hc]
        simp [etaL, dotsL, whL]
      rw [plcL_comp_of_mem μ [] [up i] (dcapRHS_mem cs i ν n) (etaL_mem i ν n), Category.assoc,
        Category.assoc, ← Category.assoc (plcL D Sc μ [] [up i] [] [dn i, up i] _), he,
        show (cl D Sc μ [up i] [dn i, up i, up i]
            ([([], Shape.cup i, [up i])] ++ dotsL [dn i] i [up i] n ++ [([dn i], Shape.cross i i, [])]) ≫
              leps cs i μ) = curl18 cs i μ n from rfl,
        curl18_eq_zero cs i μ n (by omega), Limits.comp_zero]
    rw [sum_eq_zero hz, zero_sub]
    congr 1
    rw [List.map_nil]
    exact congrArg (· ≫ leps cs i μ) (by rw [cl_nil, Category.id_comp])
  rw [← neg_neg (cl D Sc μ [dn i, up i, up i] [dn i, up i, up i] [([dn i], Shape.cross i i, [])] ≫
    leps cs i μ), ← claim, ← Preadditive.comp_neg, eq_6_3 cs i μ hh, Preadditive.comp_sub,
    Linear.comp_smul]
  rw [sub_eq_self]
  rw [dsc]
  split_ifs with h1
  · have hz : cl D Sc μ [dn i, up i, up i] [up i, dn i, up i] [([], Shape.lcross i i, [up i])] ≫
        cl D Sc μ [up i, dn i, up i] [up i] [([], Shape.cap i, [up i])] = 0 := by
      have E := congrArg (plcL D Sc μ [] [up i] [dn i, up i] [])
        (cl_invP₃ Sc i ν 0 (by rw [hνh]; omega))
      rw [plcL_cl, map_zero] at E
      rw [cl_comp hl (by simp [Shape.dom, Shape.cod])]
      refine Eq.trans ?_ E
      congr 1
    rw [hz, smul_zero]
  · rw [zero_smul]

end OddMath.SKM
