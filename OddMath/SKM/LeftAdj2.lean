/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.LeftAdj

/-!
# Pitchfork relations for the leftward cups (Brundan–Ellis, Lemma 6.1 (6.2))

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §6, Lemma 6.1 (6.2)
and the claim used for it in the proof ("one first checks that ... when `h ≥ -1`").

On `Eᵢ 1_λ` (rightmost region `λ = μ`, `ν = λ + αᵢ`, `h = ⟨hᵢ,λ⟩`):

* `leta`: `η'` (at `ν`) on the left of the strand; `reta` (from `OddMath.SKM.CurlsR`): `η'` (at `λ`)
  on the right;
* `L62`: `η'` on the right, then the strand crossing both legs of the cup (`τ`, then `σ`);
* `claim_6_2` : for `h ≥ -1`, `-L62 = leta - δ_{h,-1} c_{λ;i} (↑ ⊗ η)`, proved by testing against the
  isomorphism (1.13) at `ν` (`ext_EFE'`), the mirror image of the proof of (6.3);
* (6.2) (`eq_6_2`);
* Proposition 6.2, first relation of (6.6) (`eq_6_6_a`): `η'` on the left followed by `ε'` on the
  right is `(-1)^{|i,λ|}` times the identity of `Eᵢ 1_λ` (cases `h ≥ 0` via (2.11), (6.2), (5.20);
  `h ≤ -2` via (2.10), (6.1), (5.18); `h = -1` via (5.4), (5.15), (2.4), (6.1), (1.7), as in the
  paper).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Finset

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- `η'` (at `λ + αᵢ`) to the left of `Eᵢ 1_λ`. -/
def leta (i : I) (μ : X) :
    (pres D Sc).obj (ob D μ [up i]) ⟶ (pres D Sc).obj (ob D μ [up i, dn i, up i]) :=
  plcL D Sc μ [] [up i] [] [up i, dn i] (etaP cs i (wt D μ [up i]))

/-- The strand crossing the two legs of a cup on its right: `τ`, then `σ`. -/
def crossEF (i : I) : List (LayerData I) :=
  [([], Shape.cross i i, [dn i])] ++ (sigmaL i i).map (whL [up i] [])

theorem sChain_crossEF (i : I) : SChain [up i, up i, dn i] (crossEF i) [up i, dn i, up i] :=
  (show SChain [up i, up i, dn i] [([], Shape.cross i i, [dn i])] [up i, up i, dn i] by
    simp [Shape.dom, Shape.cod]).append
    (by simpa using (sChain_sigmaL i i).whisk [up i] [])

/-- The left-hand side of the claim for (6.2) (without the sign). -/
def L62 (i : I) (μ : X) :
    (pres D Sc).obj (ob D μ [up i]) ⟶ (pres D Sc).obj (ob D μ [up i, dn i, up i]) :=
  reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i, dn i, up i] (crossEF i)

/-- The scalar `δ_{⟨hᵢ,λ⟩,-1} c_{λ;i}`. -/
def dsc' (i : I) (μ : X) : k := if D.h i μ = -1 then (cs.c μ i : k) else 0

/-- `σ` on the two left strands of `Eᵢ Fᵢ Eᵢ`. -/
abbrev S1 (i : I) (μ : X) :
    (pres D Sc).obj (ob D μ [up i, dn i, up i]) ⟶ (pres D Sc).obj (ob D μ [dn i, up i, up i]) :=
  cl D Sc μ [up i, dn i, up i] [dn i, up i, up i] ((sigmaL i i).map (whL [] [up i]))

/-- The rightward cap with `m` dots on its upward leg, on the two left strands of `Eᵢ Fᵢ Eᵢ`. -/
abbrev S2 (i : I) (μ : X) (m : ℕ) :
    (pres D Sc).obj (ob D μ [up i, dn i, up i]) ⟶ (pres D Sc).obj (ob D μ [up i]) :=
  cl D Sc μ [up i, dn i, up i] [up i] ((epsL i m).map (whL [] [up i]))

/-- Maps into `Eᵢ Fᵢ Eᵢ 1_λ` with `⟨hᵢ,λ+αᵢ⟩ ≥ 0` are determined by their composites with `σ ⊗ ↑` and
with the dotted caps `(ε ∘ (xᵐ ⊗ 1)) ⊗ ↑`, `m < ⟨hᵢ,λ+αᵢ⟩` (the isomorphism (1.13) at `λ + αᵢ`). -/
theorem ext_EFE' (i : I) (μ : X) (hh : 0 ≤ D.h i (wt D μ [up i])) {Z : (pres D Sc).Presented}
    {f g : Z ⟶ (pres D Sc).obj (ob D μ [up i, dn i, up i])}
    (h₁ : f ≫ S1 i μ = g ≫ S1 i μ)
    (h₂ : ∀ m : ℕ, (m : ℤ) < D.h i (wt D μ [up i]) → f ≫ S2 i μ m = g ≫ S2 i μ m) : f = g := by
  have E : -cl D Sc μ [up i, dn i, up i] [up i, dn i, up i]
        ((sigmaL i i ++ lcrossL i i).map (whL [] [up i])) +
      ∑ n ∈ range (D.h i (wt D μ [up i])).toNat, cl D Sc μ [up i, dn i, up i] [up i, dn i, up i]
        ((epsL i n ++ dcupL i n).map (whL [] [up i])) =
      cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] [] := by
    have E0 := congrArg (plcL D Sc μ [] [up i] [up i, dn i] [up i, dn i])
      (cl_invP₁ Sc i (wt D μ [up i]) hh)
    simp only [map_add, map_neg, map_sum, plcL_cl] at E0
    exact E0
  have hs : SChain [up i, dn i, up i] ((sigmaL i i).map (whL [] [up i])) [dn i, up i, up i] := by
    simpa using (sChain_sigmaL i i).whisk [] [up i]
  have hl : SChain [dn i, up i, up i] ((lcrossL i i).map (whL [] [up i])) [up i, dn i, up i] := by
    simpa using (sChain_lcrossL i i).whisk [] [up i]
  have he : ∀ n, SChain [up i, dn i, up i] ((epsL i n).map (whL [] [up i])) [up i] := fun n => by
    simpa using (sChain_epsL i n).whisk [] [up i]
  have hd : ∀ n, SChain [up i] ((dcupL i n).map (whL [] [up i])) [up i, dn i, up i] := fun n => by
    simpa using (sChain_dcupL i n).whisk [] [up i]
  have hid : 𝟙 ((pres D Sc).obj (ob D μ [up i, dn i, up i])) =
      -(S1 i μ ≫ cl D Sc μ [dn i, up i, up i] [up i, dn i, up i] ((lcrossL i i).map (whL [] [up i]))) +
      ∑ n ∈ range (D.h i (wt D μ [up i])).toNat,
        S2 i μ n ≫ cl D Sc μ [up i] [up i, dn i, up i] ((dcupL i n).map (whL [] [up i])) := by
    rw [← cl_nil μ [up i, dn i, up i], ← E, cl_comp hs hl, List.map_append]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [cl_comp (he n) (hd n), List.map_append]
  rw [← Category.comp_id f, ← Category.comp_id g, hid]
  simp only [Preadditive.comp_add, Preadditive.comp_neg, Preadditive.comp_sum, ← Category.assoc, h₁]
  congr 1
  refine sum_congr rfl fun n hn => ?_
  rw [mem_range] at hn
  rw [h₂ n (by omega)]

theorem T2_crossFE (i : I) (μ : X) (m : ℕ) :
    T2 i μ m ≫ cl D Sc μ [up i, dn i, up i] [dn i, up i, up i] (crossFE i) =
      -∑ s ∈ range m, zsign k (D.parity i * (m - 1 - s : ℕ) * (D.parity i * s) + D.parity i * s) •
        (cl D Sc μ [up i] [up i] (dotsL [] i [] s) ≫ cl D Sc μ [up i] [dn i, up i, up i]
          ([([], Shape.cup i, [up i])] ++ dotsL [dn i] i [up i] (m - 1 - s) ++
            [([dn i], Shape.cross i i, [])])) := by
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
  rw [cl_comp he (sChain_crossFE i), e1, ← E', E2,
    cup_plc_up2 i μ hX, L1', map_neg, map_smul, map_sum, Preadditive.comp_neg,
    Linear.comp_smul, Preadditive.comp_sum, smul_neg, smul_smul, smul_sum]
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
  simp only [Linear.comp_smul, smul_smul]
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
    ← cl_comp hdr hZ]
  congr 1
  simp only [← zsign_add]
  congr 1
  generalize D.parity i = a; generalize (n : ZMod 2) = x; generalize (s : ZMod 2) = y
  generalize (m : ZMod 2) = z
  revert a x y z; decide


/-- `η'` on the right followed by `σ` on the two right strands: by (5.17). -/
theorem reta_sigma (i : I) (μ : X) :
    reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i, dn i, up i] ((sigmaL i i).map (whL [up i] [])) =
      -∑ n ∈ range ((-D.h i (wt D μ [])).toNat + 1), zsign k (D.parity i * ((n + 1 : ℕ) : ZMod 2)) •
        (rbub i μ (bubL cs i (wt D μ []) (-(n : ℤ) - 1)) ≫ T2 i μ n) := by
  have e : cl D Sc μ [up i, up i, dn i] [up i, dn i, up i] ((sigmaL i i).map (whL [up i] [])) =
      plcL D Sc μ [up i] [] [up i, dn i] [dn i, up i]
        (cl D Sc (wt D μ []) [up i, dn i] [dn i, up i] (sigmaL i i)) := by
    rw [plcL_cl]; rfl
  rw [e, reta, ← plcL_comp_of_mem μ [up i] [] (etaP_mem cs i _) (sigma_mem i _), eq_5_17_b, map_neg,
    map_sum]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [map_smul, plcL_comp_of_mem μ [up i] [] (bubL_mem cs i _ _) (etaL_mem i _ n), plcL_cl]
  rfl

/-- The mirror image of (6.4): the composite of the claim for (6.2) with `σ ⊗ ↑`. -/
theorem check_6_2a (i : I) (μ : X) (hh : -1 ≤ D.h i μ) :
    (-(L62 cs i μ)) ≫ S1 i μ = (leta cs i μ - dsc' cs i μ •
      cl D Sc μ [up i] [up i, dn i, up i] [([up i], Shape.cup i, [])]) ≫ S1 i μ := by
  have hR1 : leta cs i μ ≫ S1 i μ = 0 := by
    have e : S1 i μ = plcL D Sc μ [] [up i] [up i, dn i] [dn i, up i]
        (cl D Sc (wt D μ [up i]) [up i, dn i] [dn i, up i] (sigmaL i i)) := by
      rw [plcL_cl]; rfl
    rw [e, leta, ← plcL_comp_of_mem μ [] [up i] (etaP_mem cs i _) (sigma_mem i _),
      eq_2_13_a cs i _ (by rw [h_wt_up]; omega), map_zero]
  have hR2 : cl D Sc μ [up i] [up i, dn i, up i] [([up i], Shape.cup i, [])] ≫ S1 i μ =
      cl D Sc μ [up i] [dn i, up i, up i] (curlLList i) := by
    rw [cl_comp (by simp [Shape.dom, Shape.cod]) (by simpa using (sChain_sigmaL i i).whisk [] [up i]),
      eq_2_4_b]
    rfl
  have hL : L62 cs i μ ≫ S1 i μ = reta cs i μ ≫
      cl D Sc μ [up i, up i, dn i] [up i, dn i, up i] ((sigmaL i i).map (whL [up i] [])) ≫
        cl D Sc μ [up i, dn i, up i] [dn i, up i, up i] (crossFE i) := by
    have E8 := lemma33_eq8 Sc i i i μ (by simp)
    have hs : SChain [up i, up i, dn i] ((sigmaL i i).map (whL [up i] [])) [up i, dn i, up i] := by
      simpa using (sChain_sigmaL i i).whisk [up i] []
    have h4 : SChain [up i, dn i, up i] ((sigmaL i i).map (whL [] [up i])) [dn i, up i, up i] := by
      simpa using (sChain_sigmaL i i).whisk [] [up i]
    have e1 : crossEF i ++ (sigmaL i i).map (whL [] [up i]) = lemma33_eq8_rhs i i i := by
      simp [lemma33_eq8_rhs, crossEF, crossL]
    have e2 : lemma33_eq8_lhs i i i = (sigmaL i i).map (whL [up i] []) ++ crossFE i := by
      simp [lemma33_eq8_lhs, crossFE, crossL]
    rw [L62, Category.assoc, cl_comp (sChain_crossEF i) h4, e1, ← E8, e2, ← cl_comp hs (sChain_crossFE i)]
  rw [Preadditive.sub_comp, Linear.smul_comp, hR1, hR2, zero_sub, Preadditive.neg_comp, hL,
    ← Category.assoc, reta_sigma, Preadditive.neg_comp, Preadditive.sum_comp, neg_neg]
  simp only [Linear.smul_comp, Category.assoc, T2_crossFE, Preadditive.comp_neg, smul_neg,
    Preadditive.comp_sum, Linear.comp_smul]
  rcases eq_or_lt_of_le hh with h1 | h1
  · have hM : (-D.h i (wt D μ [])).toNat = 1 := by simp only [wt_nil]; omega
    rw [hM, sum_range_succ, sum_range_one, sum_range_zero, smul_zero, neg_zero, zero_add,
      sum_range_one, dsc', ite_eq_left h1.symm]
    have hb : bubL cs i (wt D μ []) (-((1 : ℕ) : ℤ) - 1) = (cs.c μ i : k) • 𝟙 _ := by
      rw [show -((1 : ℕ) : ℤ) - 1 = D.h i (wt D μ []) - 1 by simp only [wt_nil]; omega, bubL_eq_c]
      rfl
    rw [hb, rbub, map_smul, ← rbub, rbub_id]
    simp only [dotsL, List.replicate_zero, cl_nil, Category.id_comp,
      Linear.smul_comp, Nat.cast_zero, mul_zero, add_zero, zsign_zero, smul_smul]
    rw [show (1 - 1 - 0 : ℕ) = 0 from rfl, List.replicate_zero, List.append_nil]
    congr 2
    rw [show ((1 + 1 : ℕ) : ZMod 2) = 0 from rfl, mul_zero, zsign_zero, one_mul, one_mul]
  · have hM : (-D.h i (wt D μ [])).toNat = 0 := by simp only [wt_nil]; omega
    rw [hM, sum_range_one, sum_range_zero, smul_zero, neg_zero, dsc', ite_eq_right (by omega),
      zero_smul, neg_zero]


/-- The right curl with `s` dots on the loop after the crossing (the left-hand side of (5.20)). -/
abbrev curl20 (i : I) (μ : X) (s : ℕ) :
    (pres D Sc).obj (ob D μ [up i]) ⟶ (pres D Sc).obj (ob D μ [up i]) :=
  reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i]
    ([([], Shape.cross i i, [dn i])] ++ dotsL [up i] i [dn i] s ++ [([up i], Shape.cap i, [])])

theorem curl20_eq_zero (i : I) (μ : X) (s : ℕ) (hs : (s : ℤ) < D.h i μ) : curl20 cs i μ s = 0 := by
  rw [curl20, eq_5_20, show ((s : ℤ) - D.h i μ + 1).toNat = 0 by omega, sum_range_zero, neg_zero]

theorem curl20_eq_h (i : I) (μ : X) (s : ℕ) (hs : (s : ℤ) = D.h i μ) :
    curl20 cs i μ s = (-(zsign k (D.parity i) * (cs.c μ i : k))) • 𝟙 _ := by
  rw [curl20, eq_5_20, show ((s : ℤ) - D.h i μ + 1).toNat = 1 by omega, sum_range_one,
    show (s : ℤ) - ((0 : ℕ) : ℤ) - 1 = D.h i μ - 1 by omega]
  have hb : rbub i μ (bubL cs i μ (D.h i μ - 1)) = (cs.c μ i : k) • 𝟙 _ := by
    rw [bubL_eq_c, rbub, map_smul, ← rbub]
    exact congrArg _ (rbub_id i μ)
  rw [hb, dotsL, List.replicate_zero, cl_nil, Category.id_comp, smul_smul, ← neg_smul]
  simp

/-- The mirror image of (6.5): the composite of the claim for (6.2) with the dotted caps. -/
theorem check_6_2b (i : I) (μ : X) (hh : -1 ≤ D.h i μ) (m : ℕ)
    (hm : (m : ℤ) < D.h i (wt D μ [up i])) :
    (-(L62 cs i μ)) ≫ S2 i μ m = (leta cs i μ - dsc' cs i μ •
      cl D Sc μ [up i] [up i, dn i, up i] [([up i], Shape.cup i, [])]) ≫ S2 i μ m := by
  have hν : D.h i (wt D μ [up i]) = D.h i μ + 2 := h_wt_up i μ
  have eS2 : S2 i μ m = plcL D Sc μ [] [up i] [up i, dn i] []
      (cl D Sc (wt D μ [up i]) [up i, dn i] [] (epsL i m)) := by
    rw [plcL_cl]; rfl
  have hR1 : leta cs i μ ≫ S2 i μ m = lbub i μ (bubL cs i (wt D μ [up i]) m) := by
    rw [eS2, leta, ← plcL_comp_of_mem μ [] [up i] (etaP_mem cs i _) (epsL_mem i _ m), ← bubL_nat]
    rfl
  have hR2 : cl D Sc μ [up i] [up i, dn i, up i] [([up i], Shape.cup i, [])] ≫ S2 i μ m =
      cl D Sc μ [up i] [up i] (dotsL [] i [] m) := by
    rw [eS2]; exact cup_epsL i μ m
  have hL : L62 cs i μ ≫ S2 i μ m = zsign k (D.parity i * (m : ZMod 2)) •
      ∑ s ∈ range m, zsign k (D.parity i * (s : ZMod 2)) •
        (zsign k ((m - 1 - s : ℕ) * D.parity i * ((s : ZMod 2) * D.parity i)) •
          (curl20 cs i μ s ≫ cl D Sc μ [up i] [up i] (dotsL [] i [] (m - 1 - s)))) := by
    have e1 : crossEF i ++ (epsL i m).map (whL [] [up i]) =
        tauEEF i ++ (sigmaL i i).map (whL [up i] []) ++ (epsL i m).map (whL [] [up i]) := by
      simp [crossEF]
    rw [L62, Category.assoc, cl_comp (sChain_crossEF i)
      (by simpa using (sChain_epsL i m).whisk [] [up i]), e1, tau_sigma_epsL, tau_dots_tau,
      Linear.comp_smul, Preadditive.comp_sum]
    congr 1
    refine sum_congr rfl fun s hs => ?_
    rw [mem_range] at hs
    rw [Linear.comp_smul]
    congr 1
    have hdp : SChain [up i] (dotsL [] i [] (m - 1 - s)) [up i] := sChain_dotsL [] i [] _
    have hds : SChain [up i, dn i] (dotsL [] i [dn i] s) [up i, dn i] := sChain_dotsL [] i [dn i] s
    have Ei := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := [up i, up i, dn i]) (T := [up i])
      (tauEEF i) [([up i], Shape.cap i, [])] hdp hds
    have e2 : ∀ (a b : List (Letter I)) (r : ℕ), (dotsL [] i [] r).map (whL a b) = dotsL a i b r := by
      intro a b r; simp [dotsL, whL]
    have e3 : (dotsL [] i [dn i] s).map (whL [up i] []) = dotsL [up i] i [dn i] s := by
      simp [dotsL, whL]
    have e4 : (dotsL [] i [dn i] s).map (whL [up i] []) = dotsL [up i] i [dn i] s := e3
    rw [e2, e3, parsum_dotsL, parsum_dotsL] at Ei
    have hc : SChain [up i, up i, dn i]
        (tauEEF i ++ dotsL [up i] i [dn i] s ++ [([up i], Shape.cap i, [])]) [up i] :=
      ((sChain_tauEEF i).append (sChain_dotsL [up i] i [dn i] s)).append
        (by simp [Shape.dom, Shape.cod])
    rw [Ei, dotsL_capR, Linear.comp_smul, ← cl_comp hc hdp, ← Category.assoc]
  rw [Preadditive.neg_comp, hL, Preadditive.sub_comp, Linear.smul_comp, hR1, hR2]
  have hb : bubL cs i (wt D μ [up i]) (m : ℤ) =
      if (m : ℤ) = D.h i (wt D μ [up i]) - 1 then (cs.c μ i : k) • 𝟙 _ else 0 := by
    rw [bubL_nat, eq_2_13_c cs i _ m hm, c_wt_up]
  rw [hb]
  rcases eq_or_lt_of_le hh with h1 | h1
  · obtain rfl : m = 0 := by omega
    rw [sum_range_zero, smul_zero, neg_zero, ite_eq_left (by omega), dsc', ite_eq_left h1.symm,
      lbub, map_smul, ← lbub, lbub_id, dotsL, List.replicate_zero, cl_nil, sub_self]
  · rw [dsc', ite_eq_right (show ¬ D.h i μ = -1 by omega), zero_smul, sub_zero]
    by_cases hm' : (m : ℤ) = D.h i (wt D μ [up i]) - 1
    · rw [ite_eq_left hm', lbub, map_smul, ← lbub, lbub_id]
      obtain ⟨n0, hn0, rfl⟩ : ∃ n0 : ℕ, (n0 : ℤ) = D.h i μ ∧ m = n0 + 1 :=
        ⟨(D.h i μ).toNat, by omega, by omega⟩
      rw [sum_eq_single n0]
      · rw [curl20_eq_h cs i μ n0 hn0, show n0 + 1 - 1 - n0 = 0 by omega, dotsL,
          List.replicate_zero, cl_nil, Category.comp_id, smul_smul, smul_smul, smul_smul, ← neg_smul]
        congr 1
        rw [Nat.cast_zero, zero_mul, zero_mul, zsign_zero, mul_one]
        have e : zsign k (D.parity i * ((n0 + 1 : ℕ) : ZMod 2)) * zsign k (D.parity i * (n0 : ZMod 2)) =
            zsign k (D.parity i) := by
          rw [← zsign_add]; congr 1; push_cast
          generalize D.parity i = a; generalize (n0 : ZMod 2) = x; revert a x; decide
        linear_combination ((cs.c μ i : k) * zsign k (D.parity i)) * e +
          (cs.c μ i : k) * zsign_mul_self' (k := k) (D.parity i)
      · intro s hs hsn
        rw [mem_range] at hs
        rw [curl20_eq_zero cs i μ s (by omega), Limits.zero_comp, smul_zero, smul_zero]
      · intro h0; exfalso; exact h0 (mem_range.2 (by omega))
    · rw [ite_eq_right hm', lbub, map_zero]
      rw [sum_eq_zero (fun s hs => by
        rw [mem_range] at hs
        rw [curl20_eq_zero cs i μ s (by omega), Limits.zero_comp, smul_zero, smul_zero]),
        smul_zero, neg_zero]


/-- **The claim for (6.2)** (Brundan–Ellis, proof of Lemma 6.1): for `⟨hᵢ,λ⟩ ≥ -1`, minus the strand
crossing `η'` (on its right) equals `η'` on the left of `↑` minus `δ_{⟨hᵢ,λ⟩,-1} c_{λ;i}` times
`↑ ⊗ η`. -/
theorem claim_6_2 (i : I) (μ : X) (hh : -1 ≤ D.h i μ) :
    -(L62 cs i μ) = leta cs i μ - dsc' cs i μ •
      cl D Sc μ [up i] [up i, dn i, up i] [([up i], Shape.cup i, [])] :=
  ext_EFE' i μ (by rw [h_wt_up]; omega) (check_6_2a cs i μ hh) fun m hm => check_6_2b cs i μ hh m hm

theorem dcupRHS_mem (i : I) (μ : X) (n : ℕ) :
    dcupRHS cs i μ n ∈ homPar D Sc μ [] [up i, dn i] (D.parity i * (n : ZMod 2)) := by
  refine Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ ?_
  have h := comp_mem_homPar (bubR_mem cs i μ (-(n : ℤ) - r - 2))
    (comp_mem_homPar (etaP_mem cs i μ) (cl_mem_homPar (D := D) (Sc := Sc) (μ := μ) (sChain_dL i r) rfl))
  convert h using 2
  rw [parsum_dotsL, ipar]
  push_cast
  generalize D.parity i = a; generalize (n : ZMod 2) = x; generalize (r : ZMod 2) = y
  generalize (D.h i μ : ZMod 2) = z
  revert a x y z; decide

/-- **Brundan–Ellis, Lemma 6.1, (6.2)**: for `⟨hᵢ,λ⟩ ≥ -1`, on `Eᵢ 1_λ`, `η'` on the right followed by
the upward crossing equals `η'` on the left followed by the leftward crossing on the two right
strands. -/
theorem eq_6_2 (i : I) (μ : X) (hh : -1 ≤ D.h i μ) :
    reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i, up i, dn i] [([], Shape.cross i i, [dn i])] =
      leta cs i μ ≫ cl D Sc μ [up i, dn i, up i] [up i, up i, dn i] [([up i], Shape.lcross i i, [])] := by
  have hlc : SChain [up i, dn i, up i] [([up i], Shape.lcross i i, [])] [up i, up i, dn i] := by
    simp [Shape.dom, Shape.cod]
  have hτ : SChain [up i, up i, dn i] [([], Shape.cross i i, [dn i])] [up i, up i, dn i] := by
    simp [Shape.dom, Shape.cod]
  have claimB : L62 cs i μ ≫ cl D Sc μ [up i, dn i, up i] [up i, up i, dn i]
      [([up i], Shape.lcross i i, [])] =
      -(reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i, up i, dn i] [([], Shape.cross i i, [dn i])]) := by
    have E15 := congrArg (plcL D Sc μ [up i] [] [up i, dn i] [up i, dn i]) (eq_5_15 cs i (wt D μ []))
    have e1 : cl D Sc μ [up i, up i, dn i] [up i, dn i, up i] (crossEF i) ≫
        cl D Sc μ [up i, dn i, up i] [up i, up i, dn i] [([up i], Shape.lcross i i, [])] =
        cl D Sc μ [up i, up i, dn i] [up i, up i, dn i] [([], Shape.cross i i, [dn i])] ≫
          plcL D Sc μ [up i] [] [up i, dn i] [up i, dn i]
            (cl D Sc (wt D μ []) [up i, dn i] [up i, dn i] (sigmaL i i ++ lcrossL i i)) := by
      rw [plcL_cl]
      change _ = _ ≫ cl D Sc μ [up i, up i, dn i] [up i, up i, dn i]
        ((sigmaL i i ++ lcrossL i i).map (whL [up i] []))
      have hsl : SChain [up i, up i, dn i] ((sigmaL i i ++ lcrossL i i).map (whL [up i] []))
          [up i, up i, dn i] := by
        simpa using ((sChain_sigmaL i i).append (sChain_lcrossL i i)).whisk [up i] []
      rw [cl_comp (sChain_crossEF i) hlc, cl_comp hτ hsl]
      simp [crossEF, lcrossL, whL]
    rw [L62, Category.assoc, e1, E15, map_sub, map_sum, plcL_cl, Preadditive.comp_sub,
      Preadditive.comp_sub, Preadditive.comp_sum, Preadditive.comp_sum]
    have hz : ∀ n ∈ range (D.h i (wt D μ [])).toNat,
        reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i, up i, dn i] [([], Shape.cross i i, [dn i])] ≫
          plcL D Sc μ [up i] [] [up i, dn i] [up i, dn i]
            (cl D Sc (wt D μ []) [up i, dn i] [] (epsL i n) ≫ dcupRHS cs i (wt D μ []) n) = 0 := by
      intro n hn
      rw [mem_range] at hn
      rw [plcL_comp_of_mem μ [up i] [] (epsL_mem i _ n) (dcupRHS_mem cs i _ n), ← Category.assoc,
        ← Category.assoc, plcL_cl]
      have e2 : (reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i, up i, dn i]
          [([], Shape.cross i i, [dn i])]) ≫
          cl D Sc μ ([up i] ++ [up i, dn i] ++ []) ([up i] ++ [] ++ []) ((epsL i n).map (whL [up i] [])) =
          curl20 cs i μ n := by
        change (reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i, up i, dn i] _) ≫
          cl D Sc μ [up i, up i, dn i] [up i] ((epsL i n).map (whL [up i] [])) = _
        rw [Category.assoc, cl_comp hτ (by simpa using (sChain_epsL i n).whisk [up i] [])]
        show reta cs i μ ≫ _ = reta cs i μ ≫ _
        congr 2
        simp [epsL, dotsL, whL]
      rw [e2, curl20_eq_zero cs i μ n (by simp only [wt_nil] at hn; omega),
        Limits.zero_comp]
    rw [sum_eq_zero hz, zero_sub, List.map_nil, cl_nil]
    erw [Category.comp_id]
  rw [← neg_neg (reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i, up i, dn i]
    [([], Shape.cross i i, [dn i])]), ← claimB, ← Preadditive.neg_comp, claim_6_2 cs i μ hh,
    Preadditive.sub_comp, Linear.smul_comp, sub_eq_self, dsc']
  split_ifs with h1
  · have hz : cl D Sc μ [up i] [up i, dn i, up i] [([up i], Shape.cup i, [])] ≫
        cl D Sc μ [up i, dn i, up i] [up i, up i, dn i] [([up i], Shape.lcross i i, [])] = 0 := by
      have E := congrArg (plcL D Sc μ [up i] [] [] [up i, dn i])
        (cl_invM₃ Sc i (wt D μ []) 0 (by simp only [wt_nil]; omega))
      rw [plcL_cl, map_zero] at E
      rw [cl_comp (by simp [Shape.dom, Shape.cod]) hlc]
      refine Eq.trans ?_ E
      congr 1
    rw [hz, smul_zero]
  · rw [zero_smul]


/-! ## Proposition 6.2, first relation -/

theorem ipar_wt_up (i : I) (μ : X) : ipar D i (wt D μ [up i]) = ipar D i μ := by
  rw [ipar, ipar, h_wt_up]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl, add_zero]

/-- **Brundan–Ellis, Proposition 6.2, (6.6)**, first relation: on `Eᵢ 1_λ`, `η'` on the left
followed by `ε'` on the right is `(-1)^{|i,λ|}` times the identity. -/
theorem eq_6_6_a (i : I) (μ : X) :
    leta cs i μ ≫ reps cs i μ = zsign k (ipar D i μ) • 𝟙 _ := by
  rcases lt_trichotomy (D.h i μ) (-1) with h1 | h1 | h1
  · -- `⟨hᵢ,λ⟩ ≤ -2`: (2.10), (6.1), (5.18)
    have hν : D.h i (wt D μ [up i]) ≤ 0 := by rw [h_wt_up]; omega
    set M := (-D.h i (wt D μ [up i])).toNat with hM
    have e : leta cs i μ = (zsign k (ipar D i (wt D μ [up i])) * (cs.c μ i : k)) •
        (cl D Sc μ [up i] [dn i, up i, up i] ([([], Shape.cup i, [up i])] ++ dotsL [dn i] i [up i] M) ≫
          cl D Sc μ [dn i, up i, up i] [up i, dn i, up i] [([], Shape.lcross i i, [up i])]) := by
      rw [leta, etaP_eq_of_nonpos cs hν, map_smul, plcL_cl, c_wt_up, ← hM]
      congr 1
      change cl D Sc μ [up i] [up i, dn i, up i] ((etaL i M ++ lcrossL i i).map (whL [] [up i])) = _
      rw [cl_comp (by simpa using ((show SChain [up i] [([], Shape.cup i, [up i])] [dn i, up i, up i] by
        simp [Shape.dom, Shape.cod])).append (sChain_dotsL [dn i] i [up i] M))
        (by simp [Shape.dom, Shape.cod])]
      simp [etaL, lcrossL, dotsL, whL]
    rw [e, Linear.smul_comp, Category.assoc, ← eq_6_1 cs i μ (by omega), ← Category.assoc,
      cl_comp (by simpa using ((show SChain [up i] [([], Shape.cup i, [up i])] [dn i, up i, up i] by
        simp [Shape.dom, Shape.cod])).append (sChain_dotsL [dn i] i [up i] M))
        (by simp [Shape.dom, Shape.cod]),
      show (cl D Sc μ [up i] [dn i, up i, up i] ([([], Shape.cup i, [up i])] ++ dotsL [dn i] i [up i] M ++
        [([dn i], Shape.cross i i, [])]) ≫ leps cs i μ) = curl18 cs i μ M from rfl,
      curl18_eq_c cs i μ M (by rw [hM]; rw [h_wt_up] at hν ⊢; omega), smul_smul, ipar_wt_up,
      mul_assoc, Units.mul_inv, mul_one]
  · -- `⟨hᵢ,λ⟩ = -1`: (5.4), (5.15), (2.4), (6.1), (1.7)
    have hν : D.h i (wt D μ [up i]) = 1 := by rw [h_wt_up]; omega
    have hcup : SChain [up i] [([up i], Shape.cup i, [])] [up i, dn i, up i] := by
      simp [Shape.dom, Shape.cod]
    have hr : (↑(cs.c μ i)⁻¹ : k) • 𝟙 ((pres D Sc).obj (ob D μ [up i])) =
        cl D Sc μ [up i] [up i, dn i, up i] [([up i], Shape.cup i, [])] ≫ reps cs i μ := by
      have hb : bubR cs i (wt D μ []) ((0 : ℕ) : ℤ) = (↑(cs.c μ i)⁻¹ : k) • 𝟙 _ := by
        rw [show ((0 : ℕ) : ℤ) = -D.h i (wt D μ []) - 1 by simp only [wt_nil]; omega, bubR_eq_c]
        rfl
      have h1' := congrArg (rbub i μ) hb
      have h2 := rbub_id (D := D) (Sc := Sc) i μ
      simp only [rbub] at h1' h2
      rw [map_smul, h2, bubR_nat,
        plcL_comp_of_mem μ [up i] [] (etaL_mem i _ 0) (epsP_mem cs i _), plcL_cl] at h1'
      refine h1'.symm.trans ?_
      change cl D Sc μ [up i] [up i, dn i, up i] ((etaL i 0).map (whL [up i] [])) ≫ reps cs i μ = _
      congr 2
    -- the identity of `Eᵢ Fᵢ` at `λ + αᵢ`, (5.15)
    have hd0 : dcupRHS cs i (wt D μ [up i]) 0 = (↑(cs.c μ i)⁻¹ : k) • etaP cs i (wt D μ [up i]) := by
      rw [dcupRHS, show (D.h i (wt D μ [up i]) - ((0 : ℕ) : ℤ)).toNat = 1 by rw [hν]; rfl,
        sum_range_one, show -((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) - 2 = -D.h i (wt D μ [up i]) - 1 by
          rw [hν]; rfl, bubR_eq_c, c_wt_up, dotsL, List.replicate_zero, cl_nil, Category.comp_id,
        Linear.smul_comp, Category.id_comp, smul_smul, hν]
      congr 1
      rw [show (((1 + ((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ) + 1 : ℤ)) : ZMod 2) = 0 by push_cast; rfl,
        mul_zero, zsign_zero, one_mul]
    have hsl : SChain [up i, dn i, up i] ((sigmaL i i ++ lcrossL i i).map (whL [] [up i]))
        [up i, dn i, up i] := by
      simpa using ((sChain_sigmaL i i).append (sChain_lcrossL i i)).whisk [] [up i]
    have E15 : cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] ((sigmaL i i ++ lcrossL i i).map (whL [] [up i])) =
        S2 i μ 0 ≫ ((↑(cs.c μ i)⁻¹ : k) • leta cs i μ) - 𝟙 _ := by
      have E := congrArg (plcL D Sc μ [] [up i] [up i, dn i] [up i, dn i]) (eq_5_15 cs i (wt D μ [up i]))
      rw [hν, show (1 : ℤ).toNat = 1 from rfl, sum_range_one, map_sub,
        plcL_comp_of_mem μ [] [up i] (epsL_mem i _ 0) (dcupRHS_mem cs i _ 0), hd0, map_smul] at E
      simp only [plcL_cl, List.map_nil] at E
      rw [cl_nil] at E
      exact E
    have hcupL : SChain [up i] [([], Shape.cup i, [up i])] [dn i, up i, up i] := by
      simp [Shape.dom, Shape.cod]
    have hτ2 : SChain [dn i, up i, up i] [([dn i], Shape.cross i i, [])] [dn i, up i, up i] := by
      simp [Shape.dom, Shape.cod]
    have hlc : SChain [dn i, up i, up i] [([], Shape.lcross i i, [up i])] [up i, dn i, up i] := by
      simp [Shape.dom, Shape.cod]
    have hB : cl D Sc μ [up i] [up i, dn i, up i] [([up i], Shape.cup i, [])] ≫
        cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] ((sigmaL i i ++ lcrossL i i).map (whL [] [up i])) ≫
        reps cs i μ = 0 := by
      have E2 := cl_step (D := D) (Sc := Sc) μ (s₀ := [up i]) (t₀ := [up i, dn i, up i])
        [] [([], Shape.lcross i i, [up i])] [] [] (eq_2_4_b Sc i i μ)
        (L := [([up i], Shape.cup i, [])] ++ (sigmaL i i ++ lcrossL i i).map (whL [] [up i]))
        (L' := ([([], Shape.cup i, [up i])] ++ [([dn i], Shape.cross i i, [])]) ++
          [([], Shape.lcross i i, [up i])])
        rfl hlc (by simp [lcrossL, whL]) (by simp)
      rw [← Category.assoc, cl_comp hcup hsl, E2, ← cl_comp (hcupL.append hτ2) hlc, Category.assoc,
        ← eq_6_1 cs i μ (by omega), ← Category.assoc, cl_comp (hcupL.append hτ2) hτ2]
      have E := congrArg (plcL D Sc μ [dn i] [] [up i, up i] [up i, up i]) (cl_quadEq Sc i (wt D μ []))
      rw [plcL_cl, map_zero] at E
      have E' : cl D Sc μ [dn i, up i, up i] [dn i, up i, up i]
          ([([dn i], Shape.cross i i, [])] ++ [([dn i], Shape.cross i i, [])]) = 0 := by
        refine Eq.trans ?_ E
        congr 1
      rw [List.append_assoc, ← cl_comp hcupL (hτ2.append hτ2), E', Limits.comp_zero,
        Limits.zero_comp]
    have key : (↑(cs.c μ i)⁻¹ : k) • 𝟙 ((pres D Sc).obj (ob D μ [up i])) =
        (↑(cs.c μ i)⁻¹ : k) • (leta cs i μ ≫ reps cs i μ) := by
      have hid : 𝟙 ((pres D Sc).obj (ob D μ [up i, dn i, up i])) =
          S2 i μ 0 ≫ ((↑(cs.c μ i)⁻¹ : k) • leta cs i μ) -
          cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] ((sigmaL i i ++ lcrossL i i).map (whL [] [up i])) := by
        rw [E15]; abel
      have hcs : cl D Sc μ [up i] [up i, dn i, up i] [([up i], Shape.cup i, [])] ≫ S2 i μ 0 = 𝟙 _ := by
        have := cup_epsL (D := D) (Sc := Sc) i μ 0
        rw [plcL_cl] at this
        refine this.trans ?_
        exact cl_nil μ [up i]
      rw [hr]
      conv_lhs => rw [← Category.id_comp (reps cs i μ), hid]
      rw [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc, hB, sub_zero, ← Category.assoc,
        ← Category.assoc, hcs, Category.id_comp, Linear.smul_comp]
    have hc : IsUnit ((↑(cs.c μ i)⁻¹ : k)) := Units.isUnit _
    rw [ipar, h1, show ((-1 : ℤ) : ZMod 2) + 1 = 0 by push_cast; rfl, mul_zero, zsign_zero, one_smul]
    exact ((hc.smul_left_cancel).mp key).symm
  · -- `⟨hᵢ,λ⟩ ≥ 0`: (2.11), (6.2), (5.20)
    have hh : 0 ≤ D.h i μ := by omega
    set N := (D.h i μ).toNat with hN
    have hlc : SChain [up i, dn i, up i] [([up i], Shape.lcross i i, [])] [up i, up i, dn i] := by
      simp [Shape.dom, Shape.cod]
    have e : reps cs i μ = (-(zsign k (D.parity i * (D.h i μ : ZMod 2))) * (↑(cs.c μ i)⁻¹ : k)) •
        (cl D Sc μ [up i, dn i, up i] [up i, up i, dn i] [([up i], Shape.lcross i i, [])] ≫
          cl D Sc μ [up i, up i, dn i] [up i] ((epsL i N).map (whL [up i] []))) := by
      rw [reps, epsP_eq_of_nonneg cs (show 0 ≤ D.h i (wt D μ []) from hh), map_smul, plcL_cl]
      congr 1
      change cl D Sc μ [up i, dn i, up i] [up i] ((lcrossL i i ++ epsL i N).map (whL [up i] [])) = _
      rw [cl_comp hlc (by simpa using (sChain_epsL i N).whisk [up i] [])]
      simp [lcrossL, whL]
    have hτ : SChain [up i, up i, dn i] [([], Shape.cross i i, [dn i])] [up i, up i, dn i] := by
      simp [Shape.dom, Shape.cod]
    rw [e, Linear.comp_smul, ← Category.assoc, ← eq_6_2 cs i μ (by omega), Category.assoc,
      cl_comp hτ (by simpa using (sChain_epsL i N).whisk [up i] [])]
    have e2 : reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i]
        ([([], Shape.cross i i, [dn i])] ++ (epsL i N).map (whL [up i] [])) = curl20 cs i μ N := by
      show reta cs i μ ≫ _ = reta cs i μ ≫ _
      congr 2
      simp [epsL, dotsL, whL]
    rw [e2, curl20_eq_h cs i μ N (by omega), smul_smul]
    congr 1
    rw [ipar, mul_add, mul_one, zsign_add]
    have hc : (↑(cs.c μ i)⁻¹ : k) * (cs.c μ i : k) = 1 := Units.inv_mul _
    linear_combination (zsign k (D.parity i * ↑(D.h i μ)) * zsign k (D.parity i)) * hc

end OddMath.SKM
