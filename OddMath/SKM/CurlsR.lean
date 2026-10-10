/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Curls

/-!
# Dotted right curls (Brundan–Ellis, Corollary 5.4, (5.20), (5.21))

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Corollary 5.4,
(5.20), (5.21).

On `Eᵢ 1_λ` (rightmost region `λ = μ`): the right curl (`curlRList`) is `η'` on the right of the
strand (`reta`), the upward crossing on the two upward strands, then the rightward cap `ε` on the
right.

* `curlR_eq`: the right curl without dots is
  `-∑_{n=0}^{-⟨hᵢ,λ⟩} (-1)^{|i|(n+1)}` (the counterclockwise bubble with `-n-1` dots on the right,
  `rbub`) then (`n` dots on the strand) — from (5.17) (`η' ≫ σ`) and the zigzag relation;
* (5.20) (`eq_5_20'`): `n` dots on the loop after the crossing;
* (5.21) (`eq_5_21'`): `n` dots on the loop before the crossing.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Finset

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- `η'` placed to the right of `Eᵢ 1_λ`. -/
def reta (i : I) (μ : X) : (pres D Sc).obj (ob D μ [up i]) ⟶ (pres D Sc).obj (ob D μ [up i, up i, dn i]) :=
  plcL D Sc μ [up i] [] [] [up i, dn i] (etaP cs i (wt D μ []))

/-- A closed 2-morphism at `λ` placed to the right of `Eᵢ 1_λ`. -/
def rbub (i : I) (μ : X)
    (b : (pres D Sc).obj (ob D (wt D μ []) []) ⟶ (pres D Sc).obj (ob D (wt D μ []) [])) :
    (pres D Sc).obj (ob D μ [up i]) ⟶ (pres D Sc).obj (ob D μ [up i]) :=
  plcL D Sc μ [up i] [] [] [] b

/-- The layers of the right curl after `η'`: the upward crossing, then the cap `ε` on the right. -/
def curlRList (i : I) : List (LayerData I) :=
  [([], Shape.cross i i, [dn i]), ([up i], Shape.cap i, [])]

theorem sChain_curlRList (i : I) : SChain [up i, up i, dn i] (curlRList i) [up i] := by
  simp [curlRList, Shape.dom, Shape.cod]

/-- `σ` on the right of an upward strand followed by the cap `ε` on the left equals the crossing
followed by the cap `ε` on the right (the zigzag relation). -/
theorem curlRList_eq_sigma (i : I) (μ : X) :
    cl D Sc μ [up i, up i, dn i] [up i] (curlRList i) =
      plcL D Sc μ [up i] [] [up i, dn i] [dn i, up i]
          (cl D Sc (wt D μ []) [up i, dn i] [dn i, up i] (sigmaL i i)) ≫
        cl D Sc μ [up i, dn i, up i] [up i] [([], Shape.cap i, [up i])] := by
  have h0 : SChain [up i, dn i, up i] [([], Shape.cap i, [up i])] [up i] := by
    simp [Shape.dom, Shape.cod]
  rw [plcL_cl]
  change _ = cl D Sc μ [up i, up i, dn i] [up i, dn i, up i] ((sigmaL i i).map (whL [up i] [])) ≫ _
  rw [cl_comp (by simpa using (sChain_sigmaL i i).whisk [up i] []) h0]
  -- the two caps
  have E1 := cl_swap_ctx' (D := D) (Sc := Sc) (μ := μ) [up i, up i, dn i] [up i]
    [([up i], Shape.cup i, [up i, dn i]), ([up i, dn i], Shape.cross i i, [dn i])] []
    [] [up i] [] (Shape.cap i) (Shape.cap i)
  -- the crossing and the left cap
  have E2 := cl_swap_ctx' (D := D) (Sc := Sc) (μ := μ) [up i, up i, dn i] [up i]
    [([up i], Shape.cup i, [up i, dn i])] [([up i], Shape.cap i, [])]
    [] [] [dn i] (Shape.cap i) (Shape.cross i i)
  -- the zigzag
  have E3 := cl_step (D := D) (Sc := Sc) μ (s₀ := [up i, up i, dn i]) (t₀ := [up i])
    [] [([], Shape.cross i i, [dn i]), ([up i], Shape.cap i, [])] [] [up i, dn i] (cl_zigE Sc i _)
    (L := [([up i], Shape.cup i, [up i, dn i]), ([], Shape.cap i, [up i, up i, dn i]),
      ([], Shape.cross i i, [dn i]), ([up i], Shape.cap i, [])])
    (L' := curlRList i) rfl (by simp [Shape.dom, Shape.cod]) (by simp [whL]) (by simp [curlRList])
  simp only [Shape.dom, Shape.cod, Shape.parity, mul_zero, zero_mul, zsign_zero, one_smul,
    List.append_nil, List.nil_append, List.cons_append] at E1 E2
  simp only [sigmaL, List.map_cons, List.map_nil, whL, List.nil_append, List.append_nil,
    List.cons_append]
  rw [E1, E2]
  exact E3.symm


/-- The cup `η` with `n` dots on its upward leg on the right of an upward strand, then the cap `ε`
on the left: `n` dots on the strand (zigzag). -/
theorem etaL_capR (i : I) (μ : X) (n : ℕ) :
    plcL D Sc μ [up i] [] [] [dn i, up i] (cl D Sc (wt D μ []) [] [dn i, up i] (etaL i n)) ≫
        cl D Sc μ [up i, dn i, up i] [up i] [([], Shape.cap i, [up i])] =
      cl D Sc μ [up i] [up i] (dotsL [] i [] n) := by
  have h0 : SChain [up i, dn i, up i] [([], Shape.cap i, [up i])] [up i] := by
    simp [Shape.dom, Shape.cod]
  rw [plcL_cl]
  change cl D Sc μ [up i] [up i, dn i, up i] ((etaL i n).map (whL [up i] [])) ≫ _ = _
  rw [cl_comp (by simpa using (sChain_etaL i n).whisk [up i] []) h0]
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := [up i]) (T := [up i])
    [([up i], Shape.cup i, [])] [] (s := [up i, dn i]) (s' := []) (t := [up i]) (t' := [up i])
    (A := [([], Shape.cap i, [])]) (B := dotsL [] i [] n) (by simp [Shape.dom, Shape.cod])
    (sChain_dotsL [] i [] n)
  simp only [parsum_cons, parsum_nil, show (Shape.cap i).parity D = 0 from rfl, add_zero,
    zero_mul, zsign_zero, one_smul] at E
  have E2 := cl_step (D := D) (Sc := Sc) μ (s₀ := [up i]) (t₀ := [up i])
    [] (dotsL [] i [] n) [] [] (cl_zigE Sc i μ)
    (L := [([up i], Shape.cup i, []), ([], Shape.cap i, [up i])] ++ dotsL [] i [] n)
    (L' := dotsL [] i [] n) rfl (sChain_dotsL [] i [] n) (by simp) (by simp)
  simp only [etaL, dotsL, List.map_replicate, List.map_cons, List.map_nil, whL,
    List.nil_append, List.append_nil, List.cons_append] at E E2 ⊢
  rw [← E]
  exact E2

/-- **The right curl** (no dots): `-∑_{n=0}^{-⟨hᵢ,λ⟩} (-1)^{|i|(n+1)}` (the counterclockwise bubble
with `-n-1` dots on the right) then (`n` dots on the strand); from (5.17). -/
theorem curlR_eq (i : I) (μ : X) :
    reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i] (curlRList i) =
      -∑ n ∈ range ((-D.h i (wt D μ [])).toNat + 1), zsign k (D.parity i * ((n + 1 : ℕ) : ZMod 2)) •
        (rbub i μ (bubL cs i (wt D μ []) (-(n : ℤ) - 1)) ≫
          cl D Sc μ [up i] [up i] (dotsL [] i [] n)) := by
  rw [curlRList_eq_sigma, ← Category.assoc, reta,
    ← plcL_comp_of_mem μ [up i] [] (etaP_mem cs i _) (sigma_mem i _), eq_5_17_b, map_neg, map_sum,
    Preadditive.neg_comp, Preadditive.sum_comp]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  rw [map_smul, Linear.smul_comp, plcL_comp_of_mem μ [up i] [] (bubL_mem cs i _ _)
    (etaL_mem i _ n), Category.assoc, etaL_capR]
  rfl


/-! ## (5.20), (5.21) -/

/-- Dots on the strand below `η'` placed on its right move above it with the sign
`(-1)^{|i,λ| n |i|}`. -/
theorem dots_reta_comm (i : I) (μ : X) (n : ℕ) :
    cl D Sc μ [up i] [up i] (dotsL [] i [] n) ≫ reta cs i μ =
      zsign k (ipar D i (wt D μ []) * ((n : ZMod 2) * D.parity i)) •
        (reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i, up i, dn i] (dotsL [] i [up i, dn i] n)) := by
  have E := plcL_right_interchange (D := D) (Sc := Sc) μ [up i] (etaP_mem cs i (wt D μ []))
    (sChain_dotsL [] i [] n)
  have e1 : (dotsL [] i [] n).map (whL [] [up i, dn i]) = dotsL [] i [up i, dn i] n := by
    simp [dotsL, whL]
  have e2 : (dotsL [] i [] n).map (whL [] []) = dotsL [] i [] n := by simp [dotsL, whL]
  rw [e1, e2, parsum_dotsL] at E
  calc cl D Sc μ [up i] [up i] (dotsL [] i [] n) ≫ reta cs i μ
      = zsign k (ipar D i (wt D μ []) * ((n : ZMod 2) * D.parity i)) •
          (zsign k (ipar D i (wt D μ []) * ((n : ZMod 2) * D.parity i)) •
            (cl D Sc μ [up i] [up i] (dotsL [] i [] n) ≫ reta cs i μ)) := by
        rw [smul_smul, zsign_mul_self', one_smul]
    _ = _ := congrArg (zsign k (ipar D i (wt D μ []) * ((n : ZMod 2) * D.parity i)) • ·) E.symm

theorem reta_dots_comm (i : I) (μ : X) (n : ℕ) :
    reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i, up i, dn i] (dotsL [] i [up i, dn i] n) =
      zsign k (ipar D i (wt D μ []) * ((n : ZMod 2) * D.parity i)) •
        (cl D Sc μ [up i] [up i] (dotsL [] i [] n) ≫ reta cs i μ) := by
  rw [dots_reta_comm, smul_smul, zsign_mul_self', one_smul]

/-- Dots on the strand and a closed 2-morphism on its right supercommute. -/
theorem bub_dots_commR (i : I) (μ : X) {p : ZMod 2}
    {b : (pres D Sc).obj (ob D (wt D μ []) []) ⟶ (pres D Sc).obj (ob D (wt D μ []) [])}
    (hb : b ∈ closedPar D Sc (wt D μ []) p) (n : ℕ) :
    rbub i μ b ≫ cl D Sc μ [up i] [up i] (dotsL [] i [] n) =
      zsign k (p * ((n : ZMod 2) * D.parity i)) •
        (cl D Sc μ [up i] [up i] (dotsL [] i [] n) ≫ rbub i μ b) := by
  have E := plcL_right_interchange (D := D) (Sc := Sc) μ [up i] hb (sChain_dotsL [] i [] n)
  have e2 : (dotsL [] i [] n).map (whL [] []) = dotsL [] i [] n := by simp [dotsL, whL]
  rw [e2, parsum_dotsL] at E
  exact E

/-- A diagram on the two upward strands of `Eᵢ Eᵢ Fᵢ 1_λ` followed by the cap `ε` on the right. -/
theorem plc_up2_capR (i : I) (μ : X) {L : List (LayerData I)}
    (hL : SChain [up i, up i] L [up i, up i]) :
    cl D Sc μ [up i, up i, dn i] [up i] (L.map (whL [] [dn i]) ++ [([up i], Shape.cap i, [])]) =
      plcL D Sc μ [] [dn i] [up i, up i] [up i, up i]
          (cl D Sc (wt D μ [dn i]) [up i, up i] [up i, up i] L) ≫
        cl D Sc μ [up i, up i, dn i] [up i] [([up i], Shape.cap i, [])] := by
  have h0 : SChain [up i, up i, dn i] [([up i], Shape.cap i, [])] [up i] := by
    simp [Shape.dom, Shape.cod]
  rw [plcL_cl]
  change _ = cl D Sc μ [up i, up i, dn i] [up i, up i, dn i] (L.map (whL [] [dn i])) ≫ _
  rw [cl_comp (by simpa using hL.whisk [] [dn i]) h0]

/-- Dots on the left strand of `Eᵢ Eᵢ Fᵢ` move above the cap `ε` on the right. -/
theorem dotsL_capR (i : I) (μ : X) (n : ℕ) (pre : List (LayerData I)) (s : List (Letter I)) :
    cl D Sc μ s [up i] (pre ++ dotsL [] i [up i, dn i] n ++ [([up i], Shape.cap i, [])]) =
      cl D Sc μ s [up i] (pre ++ [([up i], Shape.cap i, [])] ++ dotsL [] i [] n) := by
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := s) (T := [up i]) pre []
    (s := [up i]) (s' := [up i]) (t := [up i, dn i]) (t' := [])
    (A := dotsL [] i [] n) (B := [([], Shape.cap i, [])]) (sChain_dotsL [] i [] n)
    (by simp [Shape.dom, Shape.cod])
  simp only [parsum_cons, parsum_nil, show (Shape.cap i).parity D = 0 from rfl, add_zero,
    mul_zero, zsign_zero, one_smul] at E
  simp only [dotsL, List.map_replicate, List.map_cons, List.map_nil, whL, List.nil_append,
    List.append_nil] at E ⊢
  exact E

theorem reta_epsL (i : I) (μ : X) (s : ℕ) :
    reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i]
        (dotsL [up i] i [dn i] s ++ [([up i], Shape.cap i, [])]) =
      rbub i μ (bubL cs i (wt D μ []) s) := by
  rw [rbub, bubL_nat, plcL_comp_of_mem μ [up i] [] (etaP_mem cs i _) (epsL_mem i _ s), plcL_cl]
  change reta cs i μ ≫ _ = reta cs i μ ≫
    cl D Sc μ [up i, up i, dn i] [up i] ((epsL i s).map (whL [up i] []))
  congr 2
  simp [epsL, dotsL, whL]


/-- **Brundan–Ellis, (5.21)**, as a sum over `r < n + max(-⟨hᵢ,λ⟩, 0) + 1`: the right curl with `n`
dots on the loop before the crossing is `-∑_r (-1)^{|i|(r+1)}` (the counterclockwise bubble with
`n - r - 1` dots on the right) then (`r` dots on the strand). -/
theorem eq_5_21' (i : I) (μ : X) (n : ℕ) :
    reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i] (dotsL [up i] i [dn i] n ++ curlRList i) =
      -∑ r ∈ range (n + ((-D.h i (wt D μ [])).toNat + 1)),
        zsign k (D.parity i * ((r + 1 : ℕ) : ZMod 2)) •
          (rbub i μ (bubL cs i (wt D μ []) ((n : ℤ) - r - 1)) ≫
            cl D Sc μ [up i] [up i] (dotsL [] i [] r)) := by
  have hT : SChain [up i, up i] (crossL [] i i []) [up i, up i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hX : dotsL [up i] i [dn i] n ++ curlRList i =
      (dotsL [up i] i [] n ++ crossL [] i i []).map (whL [] [dn i]) ++ [([up i], Shape.cap i, [])] := by
    simp [curlRList, crossL, dotsL, whL]
  have hA : reta cs i μ ≫ plcL D Sc μ [] [dn i] [up i, up i] [up i, up i]
        (cl D Sc (wt D μ [dn i]) [up i, up i] [up i, up i] (crossL [] i i [] ++ dotsL [] i [up i] n)) ≫
      cl D Sc μ [up i, up i, dn i] [up i] [([up i], Shape.cap i, [])] =
      (reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i] (curlRList i)) ≫
        cl D Sc μ [up i] [up i] (dotsL [] i [] n) := by
    rw [← plc_up2_capR i μ (hT.append (sChain_dotsL [] i [up i] n))]
    have e : (crossL [] i i [] ++ dotsL [] i [up i] n).map (whL [] [dn i]) ++
        [([up i], Shape.cap i, [])] = [([], Shape.cross i i, [dn i])] ++ dotsL [] i [up i, dn i] n ++
          [([up i], Shape.cap i, [])] := by
      simp [crossL, dotsL, whL]
    have hdn : SChain [up i] (dotsL [] i [] n) [up i] := sChain_dotsL [] i [] n
    rw [e, dotsL_capR, Category.assoc, cl_comp (sChain_curlRList i) hdn]
    simp [curlRList]
  have hB : ∀ s ∈ range n, zsign k (D.parity i * (s : ZMod 2)) •
      (reta cs i μ ≫ plcL D Sc μ [] [dn i] [up i, up i] [up i, up i]
        (cl D Sc (wt D μ [dn i]) [up i, up i] [up i, up i]
          (dotsL [up i] i [] s ++ dotsL [] i [up i] (n - 1 - s))) ≫
      cl D Sc μ [up i, up i, dn i] [up i] [([up i], Shape.cap i, [])]) =
      zsign k (D.parity i * (s : ZMod 2)) • (rbub i μ (bubL cs i (wt D μ []) s) ≫
        cl D Sc μ [up i] [up i] (dotsL [] i [] (n - 1 - s))) := by
    intro s _
    congr 1
    rw [← plc_up2_capR i μ ((sChain_dotsL [up i] i [] s).append (sChain_dotsL [] i [up i] _))]
    have e : (dotsL [up i] i [] s ++ dotsL [] i [up i] (n - 1 - s)).map (whL [] [dn i]) ++
        [([up i], Shape.cap i, [])] = dotsL [up i] i [dn i] s ++ dotsL [] i [up i, dn i] (n - 1 - s) ++
          [([up i], Shape.cap i, [])] := by
      simp [dotsL, whL]
    have hd : SChain [up i, up i, dn i] (dotsL [up i] i [dn i] s ++ [([up i], Shape.cap i, [])])
        [up i] := (sChain_dotsL [up i] i [dn i] s).append (by simp [Shape.dom, Shape.cod])
    have hdn : SChain [up i] (dotsL [] i [] (n - 1 - s)) [up i] := sChain_dotsL [] i [] _
    rw [e, dotsL_capR, ← cl_comp hd hdn, ← Category.assoc, reta_epsL]
  have L2 := lemma31_eq2_eq Sc i (wt D μ [dn i]) n
  have L2' : cl D Sc (wt D μ [dn i]) [up i, up i] [up i, up i] (dotsL [up i] i [] n ++ crossL [] i i []) =
      zsign k (D.parity i * D.parity i * n) •
        (cl D Sc (wt D μ [dn i]) [up i, up i] [up i, up i] (crossL [] i i [] ++ dotsL [] i [up i] n) -
          ∑ s ∈ range n, zsign k (D.parity i * s) • cl D Sc (wt D μ [dn i]) [up i, up i] [up i, up i]
            (dotsL [up i] i [] s ++ dotsL [] i [up i] (n - 1 - s))) := by
    rw [← L2, sub_sub_cancel, smul_smul, zsign_mul_self', one_smul]
  rw [hX, plc_up2_capR i μ ((sChain_dotsL [up i] i [] n).append hT), L2']
  simp only [map_sub, map_sum, map_smul, Preadditive.sub_comp, Preadditive.sum_comp,
    Linear.smul_comp, Preadditive.comp_sub, Preadditive.comp_sum, Linear.comp_smul]
  rw [sum_congr rfl hB, hA, curlR_eq, Preadditive.neg_comp, Preadditive.sum_comp,
    sum_range_add _ n ((-D.h i (wt D μ [])).toNat + 1), neg_add, smul_sub, smul_neg, smul_sum,
    smul_sum, sub_eq_add_neg, add_comm]
  congr 1
  · congr 1
    conv_rhs => rw [← sum_range_reflect]
    refine sum_congr rfl fun x hx => ?_
    rw [mem_range] at hx
    rw [smul_smul, ← zsign_add]
    congr 1
    · congr 1
      rw [show n - 1 - x + 1 = n - x by omega, Nat.cast_sub (show x ≤ n by omega)]
      generalize D.parity i = a; generalize (x : ZMod 2) = y; generalize (n : ZMod 2) = z
      revert a y z; decide
    · congr 3; push_cast [Nat.cast_sub (show x ≤ n - 1 by omega)]; omega
  · congr 1
    refine sum_congr rfl fun x _ => ?_
    rw [Linear.smul_comp, Category.assoc, cl_dots_dots, smul_smul, ← zsign_add, add_comm x n]
    congr 1
    · congr 1
      push_cast
      generalize D.parity i = a; generalize (x : ZMod 2) = y; generalize (n : ZMod 2) = z
      revert a y z; decide
    · congr 3; push_cast; ring


/-- **Brundan–Ellis, (5.20)**, as a sum over `r < n + max(-⟨hᵢ,λ⟩, 0) + 1`: the right curl with `n`
dots on the loop after the crossing is `-∑_r (-1)^{|i|(⟨hᵢ,λ⟩r+1)}` (`r` dots on the strand) then
(the counterclockwise bubble with `n - r - 1` dots on the right). -/
theorem eq_5_20' (i : I) (μ : X) (n : ℕ) :
    reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i]
        ([([], Shape.cross i i, [dn i])] ++ dotsL [up i] i [dn i] n ++ [([up i], Shape.cap i, [])]) =
      -∑ r ∈ range (n + ((-D.h i (wt D μ [])).toNat + 1)),
        zsign k (D.parity i * ((D.h i (wt D μ []) : ZMod 2) * r + 1)) •
          (cl D Sc μ [up i] [up i] (dotsL [] i [] r) ≫
            rbub i μ (bubL cs i (wt D μ []) ((n : ℤ) - r - 1))) := by
  have hT : SChain [up i, up i] (crossL [] i i []) [up i, up i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hX : [([], Shape.cross i i, [dn i])] ++ dotsL [up i] i [dn i] n ++ [([up i], Shape.cap i, [])] =
      (crossL [] i i [] ++ dotsL [up i] i [] n).map (whL [] [dn i]) ++ [([up i], Shape.cap i, [])] := by
    simp [crossL, dotsL, whL]
  have hA : reta cs i μ ≫ plcL D Sc μ [] [dn i] [up i, up i] [up i, up i]
        (cl D Sc (wt D μ [dn i]) [up i, up i] [up i, up i] (dotsL [] i [up i] n ++ crossL [] i i [])) ≫
      cl D Sc μ [up i, up i, dn i] [up i] [([up i], Shape.cap i, [])] =
      zsign k (ipar D i (wt D μ []) * ((n : ZMod 2) * D.parity i)) •
        (cl D Sc μ [up i] [up i] (dotsL [] i [] n) ≫
          (reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i] (curlRList i))) := by
    rw [← plc_up2_capR i μ ((sChain_dotsL [] i [up i] n).append hT)]
    have e : (dotsL [] i [up i] n ++ crossL [] i i []).map (whL [] [dn i]) ++
        [([up i], Shape.cap i, [])] = dotsL [] i [up i, dn i] n ++ curlRList i := by
      simp [curlRList, crossL, dotsL, whL]
    have hd3 : SChain [up i, up i, dn i] (dotsL [] i [up i, dn i] n) [up i, up i, dn i] :=
      sChain_dotsL [] i [up i, dn i] n
    rw [e, ← cl_comp hd3 (sChain_curlRList i), ← Category.assoc, reta_dots_comm, Linear.smul_comp,
      Category.assoc]
  have hB : ∀ s ∈ range n, zsign k (D.parity i * (s : ZMod 2)) •
      (reta cs i μ ≫ plcL D Sc μ [] [dn i] [up i, up i] [up i, up i]
        (cl D Sc (wt D μ [dn i]) [up i, up i] [up i, up i]
          (dotsL [] i [up i] (n - 1 - s) ++ dotsL [up i] i [] s)) ≫
      cl D Sc μ [up i, up i, dn i] [up i] [([up i], Shape.cap i, [])]) =
      (zsign k (D.parity i * (s : ZMod 2)) *
          zsign k (ipar D i (wt D μ []) * (((n - 1 - s : ℕ) : ZMod 2) * D.parity i))) •
        (cl D Sc μ [up i] [up i] (dotsL [] i [] (n - 1 - s)) ≫
          rbub i μ (bubL cs i (wt D μ []) s)) := by
    intro s _
    rw [← smul_smul]
    congr 1
    rw [← plc_up2_capR i μ ((sChain_dotsL [] i [up i] _).append (sChain_dotsL [up i] i [] s))]
    have e : (dotsL [] i [up i] (n - 1 - s) ++ dotsL [up i] i [] s).map (whL [] [dn i]) ++
        [([up i], Shape.cap i, [])] = dotsL [] i [up i, dn i] (n - 1 - s) ++
          (dotsL [up i] i [dn i] s ++ [([up i], Shape.cap i, [])]) := by
      simp [dotsL, whL]
    have hd3 : SChain [up i, up i, dn i] (dotsL [] i [up i, dn i] (n - 1 - s)) [up i, up i, dn i] :=
      sChain_dotsL [] i [up i, dn i] _
    have hd : SChain [up i, up i, dn i] (dotsL [up i] i [dn i] s ++ [([up i], Shape.cap i, [])])
        [up i] := (sChain_dotsL [up i] i [dn i] s).append (by simp [Shape.dom, Shape.cod])
    rw [e, ← cl_comp hd3 hd, ← Category.assoc, reta_dots_comm, Linear.smul_comp,
      Category.assoc, reta_epsL]
  have L1 := lemma31_eq1_eq Sc i (wt D μ [dn i]) n
  have L1' : cl D Sc (wt D μ [dn i]) [up i, up i] [up i, up i] (crossL [] i i [] ++ dotsL [up i] i [] n) =
      zsign k (D.parity i * D.parity i * n) •
        (cl D Sc (wt D μ [dn i]) [up i, up i] [up i, up i] (dotsL [] i [up i] n ++ crossL [] i i []) -
          ∑ s ∈ range n, zsign k (D.parity i * s) • cl D Sc (wt D μ [dn i]) [up i, up i] [up i, up i]
            (dotsL [] i [up i] (n - 1 - s) ++ dotsL [up i] i [] s)) := by
    rw [← L1, sub_sub_cancel, smul_smul, zsign_mul_self', one_smul]
  rw [hX, plc_up2_capR i μ (hT.append (sChain_dotsL [up i] i [] n)), L1']
  simp only [map_sub, map_sum, map_smul, Preadditive.sub_comp, Preadditive.sum_comp,
    Linear.smul_comp, Preadditive.comp_sub, Preadditive.comp_sum, Linear.comp_smul]
  rw [sum_congr rfl hB, hA, curlR_eq, Preadditive.comp_neg, Preadditive.comp_sum,
    sum_range_add _ n ((-D.h i (wt D μ [])).toNat + 1), neg_add, smul_sub, smul_neg, smul_neg,
    smul_sum, smul_sum, smul_sum, sub_eq_add_neg, add_comm]
  congr 1
  · congr 1
    conv_rhs => rw [← sum_range_reflect]
    refine sum_congr rfl fun x hx => ?_
    rw [mem_range] at hx
    rw [smul_smul]
    have hnx : n = (n - 1 - x) + x + 1 := by omega
    have e3 : (n : ℤ) - ((n - 1 - x : ℕ) : ℤ) - 1 = x := by omega
    rw [e3]
    congr 1
    simp only [ipar, ← zsign_add]
    congr 1
    rw [show (n : ZMod 2) = (((n - 1 - x) + x + 1 : ℕ) : ZMod 2) by rw [← hnx]]
    push_cast
    generalize D.parity i = a; generalize (x : ZMod 2) = y
    generalize ((n - 1 - x : ℕ) : ZMod 2) = z; generalize ((D.h i (wt D μ []) : ℤ) : ZMod 2) = w
    revert a y z w; decide
  · congr 1
    refine sum_congr rfl fun x _ => ?_
    have hb := bubL_mem cs i (wt D μ []) (-(x : ℤ) - 1)
    rw [Linear.comp_smul, bub_dots_commR i μ hb, Linear.comp_smul, ← Category.assoc, cl_dots_dots,
      smul_smul, smul_smul, smul_smul]
    congr 1
    · simp only [ipar, ← zsign_add]
      congr 1
      have hpar : ((-(x : ℤ) - 1 + D.h i (wt D μ []) + 1 : ℤ) : ZMod 2) =
          ((D.h i (wt D μ []) : ℤ) : ZMod 2) + x := by
        push_cast
        generalize (x : ZMod 2) = y; generalize ((D.h i (wt D μ []) : ℤ) : ZMod 2) = z
        revert y z; decide
      rw [hpar]
      push_cast
      generalize D.parity i = a; generalize (x : ZMod 2) = y
      generalize (n : ZMod 2) = z; generalize ((D.h i (wt D μ []) : ℤ) : ZMod 2) = w
      revert a y z w; decide
    · congr 3; push_cast; ring


/-! ## (5.18)–(5.21) as printed -/

theorem sum_range_eq_of_zero {M : Type*} [AddCommMonoid M] (f : ℕ → M) {A B : ℕ} (hBA : B ≤ A)
    (hz : ∀ r, B ≤ r → r < A → f r = 0) : ∑ r ∈ range A, f r = ∑ r ∈ range B, f r := by
  symm
  apply sum_subset
  · intro r hr; rw [mem_range] at hr ⊢; omega
  · intro r hr hr'; rw [mem_range] at hr hr'; exact hz r (by omega) hr

/-- **Brundan–Ellis, Corollary 5.4, (5.18)**: for `n ≥ 0`, the left curl with `n` dots on the loop
before the crossing equals `∑_{r=0}^{n+⟨hᵢ,λ⟩+2} (-1)^{|i|⟨hᵢ,λ⟩r}` (the clockwise bubble with
`n - r - 1` dots, at `λ + αᵢ`, on the left) then (`r` dots on the strand). -/
theorem eq_5_18 (i : I) (μ : X) (n : ℕ) :
    cl D Sc μ [up i] [dn i, up i, up i]
        ([([], Shape.cup i, [up i])] ++ dotsL [dn i] i [up i] n ++ [([dn i], Shape.cross i i, [])]) ≫
        plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i (wt D μ [up i])) =
      ∑ r ∈ range ((n : ℤ) + D.h i μ + 3).toNat,
        zsign k (D.parity i * (D.h i μ : ZMod 2) * (r : ZMod 2)) •
        (lbub i μ (bubR cs i (wt D μ [up i]) ((n : ℤ) - r - 1)) ≫
          cl D Sc μ [up i] [up i] (dotsL [] i [] r)) := by
  rw [eq_5_18', h_wt_up]
  rw [sum_range_eq_of_zero _ (B := ((n : ℤ) + D.h i μ + 3).toNat) (by omega) (fun r h1 h2 => by
    rw [bubR_eq_zero_of_lt cs i _ (by rw [h_wt_up]; omega), lbub, map_zero, Limits.zero_comp,
      smul_zero])]
  refine sum_congr rfl fun r _ => ?_
  congr 2
  push_cast; rw [show (2 : ZMod 2) = 0 from rfl, add_zero]

/-- **Brundan–Ellis, Corollary 5.4, (5.19)**: for `n ≥ 0`, the left curl with `n` dots on the loop
after the crossing equals `∑_{r=0}^{n+⟨hᵢ,λ⟩+2} (-1)^{|i|r}` (`r` dots on the strand) then (the
clockwise bubble with `n - r - 1` dots, at `λ + αᵢ`, on the left). -/
theorem eq_5_19 (i : I) (μ : X) (n : ℕ) :
    cl D Sc μ [up i] [dn i, up i, up i] (curlLList i ++ dotsL [dn i] i [up i] n) ≫
        plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i (wt D μ [up i])) =
      ∑ r ∈ range ((n : ℤ) + D.h i μ + 3).toNat, zsign k (D.parity i * (r : ZMod 2)) •
        (cl D Sc μ [up i] [up i] (dotsL [] i [] r) ≫
          lbub i μ (bubR cs i (wt D μ [up i]) ((n : ℤ) - r - 1))) := by
  rw [eq_5_19', h_wt_up]
  exact sum_range_eq_of_zero _ (by omega) (fun r h1 h2 => by
    rw [bubR_eq_zero_of_lt cs i _ (by rw [h_wt_up]; omega), lbub, map_zero, Limits.comp_zero,
      smul_zero])

/-- **Brundan–Ellis, Corollary 5.4, (5.20)**: for `n ≥ 0`, the right curl with `n` dots on the loop
after the crossing equals `-∑_{r=0}^{n-⟨hᵢ,λ⟩} (-1)^{|i|(⟨hᵢ,λ⟩r+1)}` (`r` dots on the strand) then
(the counterclockwise bubble with `n - r - 1` dots on the right). -/
theorem eq_5_20 (i : I) (μ : X) (n : ℕ) :
    reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i]
        ([([], Shape.cross i i, [dn i])] ++ dotsL [up i] i [dn i] n ++ [([up i], Shape.cap i, [])]) =
      -∑ r ∈ range ((n : ℤ) - D.h i μ + 1).toNat,
        zsign k (D.parity i * ((D.h i μ : ZMod 2) * r + 1)) •
          (cl D Sc μ [up i] [up i] (dotsL [] i [] r) ≫ rbub i μ (bubL cs i μ ((n : ℤ) - r - 1))) := by
  rw [eq_5_20']
  congr 1
  exact sum_range_eq_of_zero _ (by simp only [wt_nil]; omega) (fun r h1 h2 => by
    rw [bubL_eq_zero_of_lt cs i _ (by simp only [wt_nil]; omega), rbub, map_zero,
      Limits.comp_zero, smul_zero])

/-- **Brundan–Ellis, Corollary 5.4, (5.21)**: for `n ≥ 0`, the right curl with `n` dots on the loop
before the crossing equals `-∑_{r=0}^{n-⟨hᵢ,λ⟩} (-1)^{|i|(r+1)}` (the counterclockwise bubble with
`n - r - 1` dots on the right) then (`r` dots on the strand). -/
theorem eq_5_21 (i : I) (μ : X) (n : ℕ) :
    reta cs i μ ≫ cl D Sc μ [up i, up i, dn i] [up i] (dotsL [up i] i [dn i] n ++ curlRList i) =
      -∑ r ∈ range ((n : ℤ) - D.h i μ + 1).toNat, zsign k (D.parity i * ((r + 1 : ℕ) : ZMod 2)) •
          (rbub i μ (bubL cs i μ ((n : ℤ) - r - 1)) ≫ cl D Sc μ [up i] [up i] (dotsL [] i [] r)) := by
  rw [eq_5_21']
  congr 1
  exact sum_range_eq_of_zero _ (by simp only [wt_nil]; omega) (fun r h1 h2 => by
    rw [bubL_eq_zero_of_lt cs i _ (by simp only [wt_nil]; omega), rbub, map_zero,
      Limits.zero_comp, smul_zero])

end OddMath.SKM
