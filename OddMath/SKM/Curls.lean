/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.GrassmannianCor
import OddMath.SKM.Placement

/-!
# Dotted curls (Brundan–Ellis, Corollary 5.4, (5.18)–(5.21))

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Corollary 5.4,
(5.18)–(5.21).

On `Eᵢ 1_λ` (rightmost region `λ = μ`, `ν = λ + αᵢ` the region to the left of the strand):

* the left curl (`curlL`): the rightward cup `η` on the left, the upward crossing on the two
  upward strands, then `ε'` (at `ν`) on the left; `curlL_eq`: the left curl without dots is
  `∑_{m=0}^{⟨hᵢ,ν⟩} (-1)^{|i|m}` (`m` dots on the strand) then (the clockwise bubble with `-m-1`
  dots, at `ν`, on the left) — from (5.17) at `ν` (the curl is `σ ≫ ε'` with a strand bent around
  by the zigzag relation);
* (5.18) (`eq_5_18`): `n` dots on the loop before the crossing;
* (5.19) (`eq_5_19`): `n` dots on the loop after the crossing.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Finset

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- The layers of the left curl below `ε'`: the cup `η` on the left, then the upward crossing. -/
def curlLList (i : I) : List (LayerData I) :=
  [([], Shape.cup i, [up i]), ([dn i], Shape.cross i i, [])]

theorem sChain_curlLList (i : I) : SChain [up i] (curlLList i) [dn i, up i, up i] := by
  simp [curlLList, Shape.dom, Shape.cod]

/-- The cup `η` followed by `σ` on the right of an upward strand equals the cup `η` on the left
followed by the crossing (the zigzag relation). -/
theorem curlLList_eq_sigma (i : I) (μ : X) :
    cl D Sc μ [up i] [dn i, up i, up i] (curlLList i) =
      cl D Sc μ [up i] [up i, dn i, up i] [([up i], Shape.cup i, [])] ≫
        plcL D Sc μ [] [up i] [up i, dn i] [dn i, up i]
          (cl D Sc (wt D μ [up i]) [up i, dn i] [dn i, up i] (sigmaL i i)) := by
  have h0 : SChain [up i] [([up i], Shape.cup i, [])] [up i, dn i, up i] := by
    simp [Shape.dom, Shape.cod]
  rw [plcL_cl]
  change _ = cl D Sc μ [up i] [up i, dn i, up i] _ ≫
    cl D Sc μ [up i, dn i, up i] [dn i, up i, up i] ((sigmaL i i).map (whL [] [up i]))
  rw [cl_comp h0 (by simpa using (sChain_sigmaL i i).whisk [] [up i])]
  -- the two cups
  have E1 := cl_swap_ctx' (D := D) (Sc := Sc) (μ := μ) [up i] [dn i, up i, up i] []
    [([dn i], Shape.cross i i, [dn i, up i]), ([dn i, up i], Shape.cap i, [up i])]
    [] [up i] [] (Shape.cup i) (Shape.cup i)
  -- the crossing and the second cup
  have E2 := cl_swap_ctx' (D := D) (Sc := Sc) (μ := μ) [up i] [dn i, up i, up i]
    [([], Shape.cup i, [up i])] [([dn i, up i], Shape.cap i, [up i])]
    [dn i] [] [] (Shape.cross i i) (Shape.cup i)
  -- the zigzag
  have E3 := cl_step (D := D) (Sc := Sc) μ (s₀ := [up i]) (t₀ := [dn i, up i, up i])
    [([], Shape.cup i, [up i]), ([dn i], Shape.cross i i, [])] [] [dn i, up i] [] (cl_zigE Sc i μ)
    (L := [([], Shape.cup i, [up i]), ([dn i], Shape.cross i i, []),
      ([dn i, up i, up i], Shape.cup i, []), ([dn i, up i], Shape.cap i, [up i])])
    (L' := curlLList i) (by simp [Shape.dom, Shape.cod]) rfl (by simp [whL]) (by simp [curlLList])
  simp only [Shape.dom, Shape.cod, Shape.parity, mul_zero, zsign_zero, one_smul,
    List.append_nil, List.nil_append, List.cons_append] at E1 E2
  simp only [sigmaL, List.map_cons, List.map_nil, whL, List.nil_append, List.append_nil,
    List.cons_append]
  rw [E1, E2]
  exact E3.symm


/-- The cup `η` on the right of an upward strand followed by the cap `ε` with `m` dots on its
upward leg (on the left) is `m` dots on the strand (zigzag). -/
theorem cup_epsL (i : I) (μ : X) (m : ℕ) :
    cl D Sc μ [up i] [up i, dn i, up i] [([up i], Shape.cup i, [])] ≫
        plcL D Sc μ [] [up i] [up i, dn i] [] (cl D Sc (wt D μ [up i]) [up i, dn i] [] (epsL i m)) =
      cl D Sc μ [up i] [up i] (dotsL [] i [] m) := by
  have h0 : SChain [up i] [([up i], Shape.cup i, [])] [up i, dn i, up i] := by
    simp [Shape.dom, Shape.cod]
  rw [plcL_cl]
  change cl D Sc μ [up i] [up i, dn i, up i] _ ≫
    cl D Sc μ [up i, dn i, up i] [up i] ((epsL i m).map (whL [] [up i])) = _
  rw [cl_comp h0 (by simpa using (sChain_epsL i m).whisk [] [up i])]
  -- the dots move below the cup
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := [up i]) (T := [up i]) []
    [([], Shape.cap i, [up i])] (s := [up i]) (s' := [up i]) (t := []) (t' := [dn i, up i])
    (A := dotsL [] i [] m) (B := [([], Shape.cup i, [])]) (sChain_dotsL [] i [] m) (by
      simp [Shape.dom, Shape.cod])
  simp only [parsum_cons, parsum_nil, show (Shape.cup i).parity D = 0 from rfl, add_zero,
    mul_zero, zsign_zero, one_smul] at E
  have E2 := cl_step (D := D) (Sc := Sc) μ (s₀ := [up i]) (t₀ := [up i])
    (dotsL [] i [] m) [] [] [] (cl_zigE Sc i μ)
    (L := dotsL [] i [] m ++ [([up i], Shape.cup i, []), ([], Shape.cap i, [up i])])
    (L' := dotsL [] i [] m) (sChain_dotsL [] i [] m) rfl (by simp) (by simp)
  simp only [epsL, dotsL, List.map_append, List.map_replicate, List.map_cons, List.map_nil, whL,
    List.nil_append, List.append_nil, List.cons_append, List.append_assoc] at E E2 ⊢
  rw [← E]
  exact E2

theorem sigma_mem (i : I) (μ : X) :
    cl D Sc μ [up i, dn i] [dn i, up i] (sigmaL i i) ∈
      homPar D Sc μ [up i, dn i] [dn i, up i] (parsum D (sigmaL i i)) :=
  cl_mem_homPar (sChain_sigmaL i i) rfl

theorem epsL_mem (i : I) (μ : X) (m : ℕ) :
    cl D Sc μ [up i, dn i] [] (epsL i m) ∈ homPar D Sc μ [up i, dn i] [] (parsum D (epsL i m)) :=
  cl_mem_homPar (sChain_epsL i m) rfl

/-- A closed 2-morphism at `ν = λ + αᵢ` placed to the left of `Eᵢ 1_λ`. -/
def lbub (i : I) (μ : X)
    (b : (pres D Sc).obj (ob D (wt D μ [up i]) []) ⟶ (pres D Sc).obj (ob D (wt D μ [up i]) [])) :
    (pres D Sc).obj (ob D μ [up i]) ⟶ (pres D Sc).obj (ob D μ [up i]) :=
  plcL D Sc μ [] [up i] [] [] b

/-- **The left curl** (no dots): `∑_{m=0}^{⟨hᵢ,ν⟩} (-1)^{|i|m}` (`m` dots on the strand) then
the clockwise bubble with `-m-1` dots at `ν = λ + αᵢ` on the left; from (5.17) at `ν`. -/
theorem curlL_eq (i : I) (μ : X) :
    cl D Sc μ [up i] [dn i, up i, up i] (curlLList i) ≫
        plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i (wt D μ [up i])) =
      ∑ m ∈ range ((D.h i (wt D μ [up i])).toNat + 1), zsign k (D.parity i * (m : ZMod 2)) •
        (cl D Sc μ [up i] [up i] (dotsL [] i [] m) ≫
          lbub i μ (bubR cs i (wt D μ [up i]) (-(m : ℤ) - 1))) := by
  rw [curlLList_eq_sigma, Category.assoc,
    ← plcL_comp_of_mem μ [] [up i] (sigma_mem i _) (epsP_mem cs i _), eq_5_17_a, map_sum,
    Preadditive.comp_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [map_smul, Linear.comp_smul, plcL_comp_of_mem μ [] [up i] (epsL_mem i _ m)
    (bubR_mem cs i _ _), ← Category.assoc, cup_epsL]
  rfl


/-! ## (5.19) -/

theorem dotsL_add (u : List (Letter I)) (i : I) (v : List (Letter I)) (m n : ℕ) :
    dotsL u i v m ++ dotsL u i v n = dotsL u i v (m + n) := by
  simp only [dotsL, List.replicate_add]

theorem cl_dots_dots (μ : X) (i : I) (m n : ℕ) :
    cl D Sc μ [up i] [up i] (dotsL [] i [] m) ≫ cl D Sc μ [up i] [up i] (dotsL [] i [] n) =
      cl D Sc μ [up i] [up i] (dotsL [] i [] (m + n)) := by
  have hm : SChain [up i] (dotsL [] i [] m) [up i] := sChain_dotsL [] i [] m
  have hn : SChain [up i] (dotsL [] i [] n) [up i] := sChain_dotsL [] i [] n
  rw [cl_comp hm hn, dotsL_add]

/-- A diagram on the two upward strands of `Fᵢ Eᵢ Eᵢ 1_λ`, after the cup `η` on the left. -/
theorem cup_plc_up2 (i : I) (μ : X) {L : List (LayerData I)} (hL : SChain [up i, up i] L [up i, up i]) :
    cl D Sc μ [up i] [dn i, up i, up i] ([([], Shape.cup i, [up i])] ++ L.map (whL [dn i] [])) =
      cl D Sc μ [up i] [dn i, up i, up i] [([], Shape.cup i, [up i])] ≫
        plcL D Sc μ [dn i] [] [up i, up i] [up i, up i]
          (cl D Sc (wt D μ []) [up i, up i] [up i, up i] L) := by
  have h0 : SChain [up i] [([], Shape.cup i, [up i])] [dn i, up i, up i] := by
    simp [Shape.dom, Shape.cod]
  rw [plcL_cl]
  change _ = cl D Sc μ [up i] [dn i, up i, up i] _ ≫
    cl D Sc μ [dn i, up i, up i] [dn i, up i, up i] (L.map (whL [dn i] []))
  rw [cl_comp h0 (by simpa using hL.whisk [dn i] [])]

/-- Dots on the original strand move below the cup `η` on the left. -/
theorem cup_dotsR (i : I) (μ : X) (n : ℕ) (L : List (LayerData I)) (t : List (Letter I)) :
    cl D Sc μ [up i] t ([([], Shape.cup i, [up i])] ++ dotsL [dn i, up i] i [] n ++ L) =
      cl D Sc μ [up i] t (dotsL [] i [] n ++ [([], Shape.cup i, [up i])] ++ L) := by
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := [up i]) (T := t) [] L
    (s := []) (s' := [dn i, up i]) (t := [up i]) (t' := [up i])
    (A := [([], Shape.cup i, [])]) (B := dotsL [] i [] n) (by simp [Shape.dom, Shape.cod])
    (sChain_dotsL [] i [] n)
  simp only [parsum_cons, parsum_nil, show (Shape.cup i).parity D = 0 from rfl, add_zero,
    zero_mul, zsign_zero, one_smul] at E
  simp only [dotsL, List.map_replicate, List.map_cons, List.map_nil, whL, List.nil_append,
    List.append_nil, List.cons_append] at E ⊢
  exact E


theorem etaL_mem (i : I) (μ : X) (m : ℕ) :
    cl D Sc μ [] [dn i, up i] (etaL i m) ∈ homPar D Sc μ [] [dn i, up i] (parsum D (etaL i m)) :=
  cl_mem_homPar (sChain_etaL i m) rfl

/-- The cup `η` on the left with `m` dots on its upward leg, `s` dots on the strand, then `ε'`:
`s` dots on the strand, then the clockwise bubble with `m` dots on the left. -/
theorem cup_dots_epsP (i : I) (μ : X) (s m : ℕ) :
    cl D Sc μ [up i] [dn i, up i, up i]
        ([([], Shape.cup i, [up i])] ++ dotsL [dn i, up i] i [] s ++ dotsL [dn i] i [up i] m) ≫
        plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i (wt D μ [up i])) =
      cl D Sc μ [up i] [up i] (dotsL [] i [] s) ≫
        lbub i μ (bubR cs i (wt D μ [up i]) m) := by
  rw [lbub, cup_dotsR, bubR_nat, plcL_comp_of_mem μ [] [up i] (etaL_mem i _ m) (epsP_mem cs i _),
    plcL_cl, ← Category.assoc]
  congr 1
  change _ = cl D Sc μ [up i] [up i] _ ≫ cl D Sc μ [up i] [dn i, up i, up i] _
  have hs : SChain [up i] (dotsL [] i [] s) [up i] := sChain_dotsL [] i [] s
  rw [cl_comp hs (by simpa using (sChain_etaL i m).whisk [] [up i])]
  simp [etaL, dotsL, whL]

/-- **Brundan–Ellis, (5.19)**, in the form of a sum over `r < n + max(⟨hᵢ,ν⟩, 0) + 1`: the left
curl with `n` dots on the loop after the crossing is `∑_r (-1)^{|i|r}` (`r` dots on the strand)
then the clockwise bubble with `n - r - 1` dots on the left (`ν = λ + αᵢ`, `⟨hᵢ,ν⟩ = ⟨hᵢ,λ⟩ + 2`). -/
theorem eq_5_19' (i : I) (μ : X) (n : ℕ) :
    cl D Sc μ [up i] [dn i, up i, up i] (curlLList i ++ dotsL [dn i] i [up i] n) ≫
        plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i (wt D μ [up i])) =
      ∑ r ∈ range (n + ((D.h i (wt D μ [up i])).toNat + 1)), zsign k (D.parity i * (r : ZMod 2)) •
        (cl D Sc μ [up i] [up i] (dotsL [] i [] r) ≫
          lbub i μ (bubR cs i (wt D μ [up i]) ((n : ℤ) - r - 1))) := by
  have hX : curlLList i ++ dotsL [dn i] i [up i] n =
      [([], Shape.cup i, [up i])] ++ (crossL [] i i [] ++ dotsL [] i [up i] n).map (whL [dn i] []) := by
    simp [curlLList, crossL, dotsL, whL]
  have hT : SChain [up i, up i] (crossL [] i i []) [up i, up i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hA : cl D Sc μ [up i] [dn i, up i, up i] [([], Shape.cup i, [up i])] ≫
      plcL D Sc μ [dn i] [] [up i, up i] [up i, up i]
        (cl D Sc (wt D μ []) [up i, up i] [up i, up i] (dotsL [up i] i [] n ++ crossL [] i i [])) ≫
      plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i (wt D μ [up i])) =
      cl D Sc μ [up i] [up i] (dotsL [] i [] n) ≫
        (cl D Sc μ [up i] [dn i, up i, up i] (curlLList i) ≫
          plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i (wt D μ [up i]))) := by
    rw [← Category.assoc, ← cup_plc_up2 i μ ((sChain_dotsL [up i] i [] n).append hT)]
    have e : [([], Shape.cup i, [up i])] ++ (dotsL [up i] i [] n ++ crossL [] i i []).map
        (whL [dn i] []) = [([], Shape.cup i, [up i])] ++ dotsL [dn i, up i] i [] n ++
          [([dn i], Shape.cross i i, [])] := by
      simp [dotsL, crossL, whL]
    have hn : SChain [up i] (dotsL [] i [] n) [up i] := sChain_dotsL [] i [] n
    rw [e, cup_dotsR, ← Category.assoc, cl_comp hn (sChain_curlLList i)]
    simp [curlLList, List.append_assoc]
  have hB : ∀ s ∈ range n, zsign k (D.parity i * (s : ZMod 2)) •
      (cl D Sc μ [up i] [dn i, up i, up i] [([], Shape.cup i, [up i])] ≫
      plcL D Sc μ [dn i] [] [up i, up i] [up i, up i]
        (cl D Sc (wt D μ []) [up i, up i] [up i, up i]
          (dotsL [up i] i [] s ++ dotsL [] i [up i] (n - 1 - s))) ≫
      plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i (wt D μ [up i]))) =
      zsign k (D.parity i * (s : ZMod 2)) • (cl D Sc μ [up i] [up i] (dotsL [] i [] s) ≫
        lbub i μ (bubR cs i (wt D μ [up i]) ((n : ℤ) - s - 1))) := by
    intro s hs
    rw [mem_range] at hs
    congr 1
    rw [← Category.assoc, ← cup_plc_up2 i μ ((sChain_dotsL [up i] i [] s).append
      (sChain_dotsL [] i [up i] _))]
    have e : [([], Shape.cup i, [up i])] ++ (dotsL [up i] i [] s ++ dotsL [] i [up i] (n - 1 - s)).map
        (whL [dn i] []) = [([], Shape.cup i, [up i])] ++ dotsL [dn i, up i] i [] s ++
          dotsL [dn i] i [up i] (n - 1 - s) := by
      simp [dotsL, whL]
    rw [e, cup_dots_epsP, show (n : ℤ) - s - 1 = ((n - 1 - s : ℕ) : ℤ) by omega]
  have L2 := lemma31_eq2_eq Sc i (wt D μ []) n
  rw [sub_eq_iff_eq_add] at L2
  rw [hX, cup_plc_up2 i μ (hT.append (sChain_dotsL [] i [up i] n)), L2]
  simp only [map_add, map_sum, map_smul, Preadditive.add_comp, Preadditive.sum_comp,
    Linear.smul_comp, Preadditive.comp_add, Preadditive.comp_sum, Linear.comp_smul, Category.assoc]
  rw [sum_congr rfl hB, hA, curlL_eq, Preadditive.comp_sum,
    sum_range_add _ n ((D.h i (wt D μ [up i])).toNat + 1)]
  congr 1
  · rw [smul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [Linear.comp_smul, ← Category.assoc, cl_dots_dots, smul_smul, ← zsign_add]
    congr 2
    · rw [zmod2_mul_self']; push_cast; ring
    · congr 2; push_cast; ring


/-! ## (5.18) -/

theorem h_wt_up (i : I) (μ : X) : D.h i (wt D μ [up i]) = D.h i μ + 2 := by
  simp [wt, sh, Datum.h, Datum.α, map_add, D.cd.coroot_root_self, add_comm]

/-- Dots on the strand to the right of a placed homogeneous 2-morphism `f` (of parity `p`) move
past it with the sign `(-1)^{p n |i|}`. -/
theorem dots_plc_comm (i : I) (μ : X) {s t : List (Letter I)} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D (wt D μ [up i]) s) ⟶ (pres D Sc).obj (ob D (wt D μ [up i]) t)}
    (hf : f ∈ homPar D Sc (wt D μ [up i]) s t p) (n : ℕ) :
    cl D Sc μ (s ++ [up i]) (s ++ [up i]) (dotsL s i [] n) ≫ plcL D Sc μ [] [up i] s t f =
      zsign k (p * ((n : ZMod 2) * D.parity i)) •
        (plcL D Sc μ [] [up i] s t f ≫ cl D Sc μ (t ++ [up i]) (t ++ [up i]) (dotsL t i [] n)) := by
  have E := plcL_left_interchange μ [up i] hf (sChain_dotsL [] i [] n)
  have e1 : ∀ u : List (Letter I), (dotsL [] i [] n).map (whL u []) = dotsL u i [] n := by
    intro u; simp [dotsL, whL]
  rw [e1, e1, parsum_dotsL] at E
  rw [E, smul_smul, zsign_mul_self', one_smul]

theorem dots_bub_comm (i : I) (μ : X) {p : ZMod 2}
    {b : (pres D Sc).obj (ob D (wt D μ [up i]) []) ⟶ (pres D Sc).obj (ob D (wt D μ [up i]) [])}
    (hb : b ∈ closedPar D Sc (wt D μ [up i]) p) (n : ℕ) :
    cl D Sc μ [up i] [up i] (dotsL [] i [] n) ≫ lbub i μ b =
      zsign k (p * ((n : ZMod 2) * D.parity i)) •
        (lbub i μ b ≫ cl D Sc μ [up i] [up i] (dotsL [] i [] n)) :=
  dots_plc_comm i μ hb n

/-- **Brundan–Ellis, (5.18)**, in the form of a sum over `r < n + max(⟨hᵢ,ν⟩, 0) + 1`: the left
curl with `n` dots on the loop before the crossing is `∑_r (-1)^{|i|⟨hᵢ,ν⟩r}` (the clockwise bubble
with `n - r - 1` dots on the left) then (`r` dots on the strand) (`ν = λ + αᵢ`; `⟨hᵢ,ν⟩ ≡ ⟨hᵢ,λ⟩`
mod `2`). -/
theorem eq_5_18' (i : I) (μ : X) (n : ℕ) :
    cl D Sc μ [up i] [dn i, up i, up i]
        ([([], Shape.cup i, [up i])] ++ dotsL [dn i] i [up i] n ++ [([dn i], Shape.cross i i, [])]) ≫
        plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i (wt D μ [up i])) =
      ∑ r ∈ range (n + ((D.h i (wt D μ [up i])).toNat + 1)),
        zsign k (D.parity i * (D.h i (wt D μ [up i]) : ZMod 2) * (r : ZMod 2)) •
        (lbub i μ (bubR cs i (wt D μ [up i]) ((n : ℤ) - r - 1)) ≫
          cl D Sc μ [up i] [up i] (dotsL [] i [] r)) := by
  set ν := wt D μ [up i] with hν
  have hT : SChain [up i, up i] (crossL [] i i []) [up i, up i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have hX : [([], Shape.cup i, [up i])] ++ dotsL [dn i] i [up i] n ++ [([dn i], Shape.cross i i, [])] =
      [([], Shape.cup i, [up i])] ++ (dotsL [] i [up i] n ++ crossL [] i i []).map (whL [dn i] []) := by
    simp [crossL, dotsL, whL]
  -- interchange of strand dots and `ε'`
  have hDE : ∀ m : ℕ, cl D Sc μ [dn i, up i, up i] [dn i, up i, up i] (dotsL [dn i, up i] i [] m) ≫
      plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i ν) =
      zsign k (ipar D i ν * ((m : ZMod 2) * D.parity i)) •
        (plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i ν) ≫
          cl D Sc μ [up i] [up i] (dotsL [] i [] m)) :=
    fun m => dots_plc_comm i μ (epsP_mem cs i ν) m
  have hA : cl D Sc μ [up i] [dn i, up i, up i] [([], Shape.cup i, [up i])] ≫
      plcL D Sc μ [dn i] [] [up i, up i] [up i, up i]
        (cl D Sc (wt D μ []) [up i, up i] [up i, up i] (crossL [] i i [] ++ dotsL [up i] i [] n)) ≫
      plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i ν) =
      zsign k (ipar D i ν * ((n : ZMod 2) * D.parity i)) •
        ((cl D Sc μ [up i] [dn i, up i, up i] (curlLList i) ≫
          plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i ν)) ≫
            cl D Sc μ [up i] [up i] (dotsL [] i [] n)) := by
    rw [← Category.assoc, ← cup_plc_up2 i μ (hT.append (sChain_dotsL [up i] i [] n))]
    have e : [([], Shape.cup i, [up i])] ++ (crossL [] i i [] ++ dotsL [up i] i [] n).map
        (whL [dn i] []) = curlLList i ++ dotsL [dn i, up i] i [] n := by
      simp [curlLList, crossL, dotsL, whL]
    have hd3 : SChain [dn i, up i, up i] (dotsL [dn i, up i] i [] n) [dn i, up i, up i] :=
      sChain_dotsL [dn i, up i] i [] n
    rw [e, ← cl_comp (sChain_curlLList i) hd3, Category.assoc, hDE,
      Linear.comp_smul, Category.assoc]
  have hB : ∀ s ∈ range n, zsign k (D.parity i * (s : ZMod 2)) •
      (cl D Sc μ [up i] [dn i, up i, up i] [([], Shape.cup i, [up i])] ≫
      plcL D Sc μ [dn i] [] [up i, up i] [up i, up i]
        (cl D Sc (wt D μ []) [up i, up i] [up i, up i]
          (dotsL [] i [up i] (n - 1 - s) ++ dotsL [up i] i [] s)) ≫
      plcL D Sc μ [] [up i] [dn i, up i] [] (epsP cs i ν)) =
      zsign k (D.parity i * (D.h i ν : ZMod 2) * (s : ZMod 2)) •
        (lbub i μ (bubR cs i ν ((n : ℤ) - s - 1)) ≫
          cl D Sc μ [up i] [up i] (dotsL [] i [] s)) := by
    intro s hs
    rw [mem_range] at hs
    rw [← Category.assoc, ← cup_plc_up2 i μ ((sChain_dotsL [] i [up i] _).append
      (sChain_dotsL [up i] i [] s))]
    have e : [([], Shape.cup i, [up i])] ++ (dotsL [] i [up i] (n - 1 - s) ++ dotsL [up i] i [] s).map
        (whL [dn i] []) = (etaL i (n - 1 - s)).map (whL [] [up i]) ++ dotsL [dn i, up i] i [] s := by
      simp [etaL, dotsL, whL]
    have hE : SChain [up i] ((etaL i (n - 1 - s)).map (whL [] [up i])) [dn i, up i, up i] := by
      simpa using (sChain_etaL i (n - 1 - s)).whisk [] [up i]
    have hd3 : SChain [dn i, up i, up i] (dotsL [dn i, up i] i [] s) [dn i, up i, up i] :=
      sChain_dotsL [dn i, up i] i [] s
    rw [e, ← cl_comp hE hd3, Category.assoc, hDE, Linear.comp_smul,
      ← Category.assoc, smul_smul]
    have hp : cl D Sc μ [up i] [dn i, up i, up i] ((etaL i (n - 1 - s)).map (whL [] [up i])) =
        plcL D Sc μ [] [up i] [] [dn i, up i] (cl D Sc ν [] [dn i, up i] (etaL i (n - 1 - s))) :=
      (plcL_cl D Sc μ [] [up i] [] [dn i, up i] _).symm
    rw [hp, ← plcL_comp_of_mem μ [] [up i] (etaL_mem i ν _) (epsP_mem cs i ν), ← bubR_nat,
      show ((n - 1 - s : ℕ) : ℤ) = (n : ℤ) - s - 1 by omega]
    congr 1
    rw [← zsign_add]
    congr 1
    simp only [ipar]
    generalize D.parity i = a; generalize (s : ZMod 2) = x; generalize (D.h i ν : ZMod 2) = y
    revert a x y; decide
  have L1 := lemma31_eq1_eq Sc i (wt D μ []) n
  rw [sub_eq_iff_eq_add] at L1
  rw [hX, cup_plc_up2 i μ ((sChain_dotsL [] i [up i] n).append hT), L1]
  simp only [map_add, map_sum, map_smul, Preadditive.add_comp, Preadditive.sum_comp,
    Linear.smul_comp, Preadditive.comp_add, Preadditive.comp_sum, Linear.comp_smul, Category.assoc]
  rw [sum_congr rfl hB, hA, curlL_eq, Preadditive.sum_comp,
    sum_range_add _ n ((D.h i ν).toNat + 1)]
  congr 1
  · rw [smul_sum, smul_sum]
    refine sum_congr rfl fun m _ => ?_
    have hb := bubR_mem cs i ν (-(m : ℤ) - 1)
    rw [dots_bub_comm i μ hb]
    simp only [Linear.smul_comp, Category.assoc, cl_dots_dots, smul_smul]
    rw [add_comm m n]
    congr 1
    · rw [← zsign_add, ← zsign_add, ← zsign_add]
      congr 1
      have hpar : ((-(m : ℤ) - 1 + D.h i ν + 1 : ℤ) : ZMod 2) = (D.h i ν : ZMod 2) + m := by
        push_cast
        generalize (m : ZMod 2) = x; generalize ((D.h i ν : ℤ) : ZMod 2) = y
        revert x y; decide
      rw [hpar]
      simp only [ipar]
      push_cast
      generalize D.parity i = a; generalize (m : ZMod 2) = x; generalize (n : ZMod 2) = y
      generalize (D.h i ν : ZMod 2) = z
      revert a x y z; decide
    · congr 3; push_cast; ring

end OddMath.SKM
