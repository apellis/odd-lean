/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyLeft
import OddMath.SKM.CurlsR
import OddMath.SKM.DotSlides
import OddMath.SKM.GrassmannianCor
import OddMath.SKM.Lemma31Rot
import OddMath.SKM.Lemma33Rot
import OddMath.SKM.PitchforkCup

/-!
# The alternative braid relation, unequal right colours and equal colours ([BE2] Prop 7.6)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Prop 7.6: the
braid relation for an upward, a downward and an upward strand, with the downward strand
passing on the left (`altL`) or on the right (`altR`) of the upward crossing; the crossings
between the downward and the upward strands are `σ` and the leftward crossing.

This file proves the case `i ≠ k` by sandwiching (3.8) (`lemma33_eq8`) between leftward
crossings, and the case `i = j = k`: both correction sums of the paper are computed from the
inversion relations, (5.11), (5.12), the pitchfork relations (7.5) and the left adjunction.
The first correction sum is as printed; the second has the sign `(-1)^{|i|(h + r + s)}`
instead of the printed `(-1)^{|i|(h + r + s + t)}` (ERRATA [BE2] 2). The remaining case
`i = k ≠ j` is in `OddMath.SKM.AlternativeBraid`.

Here `h = ⟨hᵢ, μ⟩` for the weight `μ` of the rightmost region.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

def altL (i j a : I) : List (LayerData I) :=
  (sigmaL i j).map (whL [] [up a]) ++ crossL [dn i] j a [] ++
    (lcrossL i a).map (whL [] [up j])
def altR (i j a : I) : List (LayerData I) :=
  (lcrossL i a).map (whL [up j] []) ++ crossL [] j a [dn i] ++
    (sigmaL i j).map (whL [up a] [])

theorem altL_chain (i j a : I) :
    SChain [up j, dn i, up a] (altL i j a) [up a, dn i, up j] :=
  ((sChain_sigmaL i j).wh [] [up a] rfl rfl).append
    ((show SChain [dn i, up j, up a] (crossL [dn i] j a []) [dn i, up a, up j] by
      simp [crossL, Shape.dom, Shape.cod]).append
      ((sChain_lcrossL i a).wh [] [up j] rfl rfl))
theorem altR_chain (i j a : I) :
    SChain [up j, dn i, up a] (altR i j a) [up a, dn i, up j] :=
  ((sChain_lcrossL i a).wh [up j] [] rfl rfl).append
    ((show SChain [up j, up a, dn i] (crossL [] j a [dn i]) [up a, up j, dn i] by
      simp [crossL, Shape.dom, Shape.cod]).append
      ((sChain_sigmaL i j).wh [up a] [] rfl rfl))

theorem alt_ne_right (i j a : I) (μ : X) (hia : i ≠ a) :
    cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altL i j a) =
      cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altR i j a) := by
  let P := (lcrossL i a).map (whL [up j] [])
  let Q := (lcrossL i a).map (whL [] [up j])
  have hp : SChain [up j, dn i, up a] P [up j, up a, dn i] :=
    (sChain_lcrossL i a).wh [up j] [] rfl rfl
  have hq : SChain [dn i, up a, up j] Q [up a, dn i, up j] :=
    (sChain_lcrossL i a).wh [] [up j] rfl rfl
  have e := cl_step (D := D) (Sc := Sc) μ P Q [] []
    (lemma33_eq8 Sc i j a (wt D μ []) (fun h => hia h.1)) hp hq
    (L := P ++ lemma33_eq8_lhs i j a ++ Q)
    (L' := P ++ lemma33_eq8_rhs i j a ++ Q)
    (by simp) (by simp)
  have eL : cl D Sc μ [up j, dn i, up a] [up a, dn i, up j]
      (P ++ lemma33_eq8_lhs i j a ++ Q) =
      cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altL i j a) := by
    apply cl_step μ [] (altL i j a) [up j] [] (cl_invNe₂ Sc i a (wt D μ []) hia)
      (by rfl) (altL_chain i j a)
    · simp [P, Q, lemma33_eq8_lhs, altL, List.append_assoc]
    · simp
  have eR : cl D Sc μ [up j, dn i, up a] [up a, dn i, up j]
      (P ++ lemma33_eq8_rhs i j a ++ Q) =
      cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altR i j a) := by
    apply cl_step μ (altR i j a) [] [] [up j]
      (cl_invNe₁ Sc i a (wt D μ [up j]) hia) (altR_chain i j a) (by rfl)
    · simp [P, Q, lemma33_eq8_rhs, altR, List.append_assoc]
    · simp
  exact eL.symm.trans (e.trans eR)

def altSandL (i j a : I) : List (LayerData I) :=
  (lcrossL i a).map (whL [up j] []) ++ lemma33_eq8_lhs i j a ++
    (lcrossL i a).map (whL [] [up j])
def altSandR (i j a : I) : List (LayerData I) :=
  (lcrossL i a).map (whL [up j] []) ++ lemma33_eq8_rhs i j a ++
    (lcrossL i a).map (whL [] [up j])

theorem altSand_eq (i j a : I) (μ : X) (h : ¬(i = a ∧ i ≠ j)) :
    cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altSandL i j a) =
      cl D Sc μ [up j, dn i, up a] [up a, dn i, up j] (altSandR i j a) := by
  exact cl_step μ ((lcrossL i a).map (whL [up j] []))
    ((lcrossL i a).map (whL [] [up j])) [] []
    (lemma33_eq8 Sc i j a (wt D μ []) h)
    ((sChain_lcrossL i a).wh [up j] [] rfl rfl)
    ((sChain_lcrossL i a).wh [] [up j] rfl rfl) (by simp [altSandL]) (by simp [altSandR])

variable (cs : CScalars Sc)

/-- First summand: counterclockwise (`bubR`, right-up) bubble at `μ + αᵢ`. -/
def altTermR (i : I) (μ : X) (r s t : ℕ) :
    (pres D Sc).obj (ob D μ [up i, dn i, up i]) ⟶
      (pres D Sc).obj (ob D μ [up i, dn i, up i]) :=
  cl D Sc μ [up i, dn i, up i] [up i] ((epsL i s).map (whL [] [up i])) ≫
    lbub i μ (bubR cs i (wt D μ [up i]) (-(r : ℤ) - s - t - 3)) ≫
    cupAt cs i μ [] [up i] ≫
    cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (dotsL [] i [dn i, up i] r) ≫
    cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (dotsL [up i, dn i] i [] t)

/-- Second summand: clockwise (`bubL`, left-up) bubble in region `μ`. -/
def altTermL (i : I) (μ : X) (r s t : ℕ) :
    (pres D Sc).obj (ob D μ [up i, dn i, up i]) ⟶
      (pres D Sc).obj (ob D μ [up i, dn i, up i]) :=
  cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (dotsL [up i, dn i] i [] r) ≫
    capAt cs i μ [up i] [] ≫
    rbub i μ (bubL cs i μ (-(r : ℤ) - s - t - 3)) ≫
    cl D Sc μ [up i] [up i, dn i, up i] ((etaL i s).map (whL [up i] [])) ≫
    cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (dotsL [] i [dn i, up i] t)

theorem altTermR_vanish (i : I) (μ : X) (r s t : ℕ)
    (h : D.h i μ < (r : ℤ) + s + t) : altTermR cs i μ r s t = 0 := by
  have hb : bubR cs i (wt D μ [up i]) (-(r : ℤ) - s - t - 3) = 0 :=
    bubR_eq_zero_of_lt cs i _ (by rw [h_wt_up]; omega)
  simp only [altTermR, hb, lbub, map_zero, Limits.zero_comp, Limits.comp_zero]

theorem altTermL_vanish (i : I) (μ : X) (r s t : ℕ)
    (h : -D.h i μ - 2 < (r : ℤ) + s + t) : altTermL cs i μ r s t = 0 := by
  have hb : bubL cs i (wt D μ []) (-(r : ℤ) - s - t - 3) = 0 :=
    bubL_eq_zero_of_lt cs i _ (by rw [wt_nil]; omega)
  have hz : rbub i μ (bubL cs i μ (-(r : ℤ) - s - t - 3)) = 0 :=
    (congrArg (plcL D Sc μ [up i] [] [] []) hb).trans
      (plcL D Sc μ [up i] [] [] []).map_zero
  simp only [altTermL, hz, Limits.zero_comp, Limits.comp_zero]

def altCorrectionR (i : I) (μ : X) :=
  ∑ r ∈ range (D.h i μ + 1).toNat, ∑ s ∈ range (D.h i μ + 1).toNat,
    ∑ t ∈ range (D.h i μ + 1).toNat,
      isg k (D.parity i) (D.h i μ + r + s + 1) • altTermR cs i μ r s t

theorem altCorrectionR_boundary (i : I) (μ : X) (h : D.h i μ = -1) :
    altCorrectionR cs i μ = 0 := by simp [altCorrectionR, h]
def altInvCorrectionR (i : I) (μ : X) :=
  ∑ n ∈ range (D.h i (wt D μ [up i])).toNat,
    ctxL D Sc μ [up i, dn i, up i] [up i, dn i, up i]
      (altR i i i) [] [up i] [] [up i, dn i] [up i, dn i]
      (cl D Sc (wt D μ [up i]) [up i, dn i] [] (epsL i n) ≫
        dcupRHS cs i (wt D μ [up i]) n)

def altInvCorrectionL (i : I) (μ : X) :=
  ∑ n ∈ range (-D.h i μ).toNat,
    ctxL D Sc μ [up i, dn i, up i] [up i, dn i, up i]
      [] [up i] [] (altL i i i) [dn i, up i] [dn i, up i]
      (dcapRHS cs i μ n ≫ cl D Sc μ [] [dn i, up i] (etaL i n))

theorem altSandR_reduce (i : I) (μ : X) :
    cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (altSandR i i i) =
      altInvCorrectionR cs i μ -
        cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (altR i i i) := by
  have e := cl_stepL (D := D) (Sc := Sc) μ
    (s₀ := [up i, dn i, up i]) (t₀ := [up i, dn i, up i]) (altR i i i) [] [] [up i]
    (eq_5_15 cs i (wt D μ [up i])) (altR_chain i i i) (by rfl)
    (L := altSandR i i i)
    (by simp [altSandR, lemma33_eq8_rhs, altR, List.append_assoc])
  rw [e, map_sub, map_sum]
  rw [ctxL_cl μ (altR_chain i i i) (by rfl)]
  simp only [List.map_nil, List.append_nil]
  rfl

theorem altSandL_reduce (i : I) (μ : X) :
    cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (altSandL i i i) =
      altInvCorrectionL cs i μ -
        cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (altL i i i) := by
  have e := cl_stepL (D := D) (Sc := Sc) μ
    (s₀ := [up i, dn i, up i]) (t₀ := [up i, dn i, up i]) [] (altL i i i) [up i] []
    (eq_5_16 cs i (wt D μ [])) (by rfl) (altL_chain i i i)
    (L := altSandL i i i)
    (by simp [altSandL, lemma33_eq8_lhs, altL, List.append_assoc])
  rw [e, map_sub, map_sum]
  rw [ctxL_cl μ (by rfl) (altL_chain i i i)]
  simp only [List.map_nil, List.nil_append]
  rfl

/-- The equal-colour case after sandwiching (3.8) between leftward crossings: the difference
is given by the inversion relations, before the ♦-cups and ♦-caps are expanded. -/
theorem alt_equal_inv (i : I) (μ : X) :
    cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (altL i i i) -
      cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (altR i i i) =
        altInvCorrectionL cs i μ - altInvCorrectionR cs i μ := by
  have e := altSand_eq (Sc := Sc) i i i μ (by simp)
  rw [altSandL_reduce cs, altSandR_reduce cs] at e
  apply (sub_eq_sub_iff_sub_eq_sub).mp
  simpa only [neg_sub] using congrArg Neg.neg e

/-- A bubble with negative dot count is a fake bubble, not zero. -/
theorem altFakeR_boundary (i : I) (μ : X) (h : D.h i μ = 0) :
    bubR cs i (wt D μ [up i]) (-3) = (↑(cs.c μ i)⁻¹ : k) • 𝟙 _ := by
  rw [show (-3 : ℤ) = -D.h i (wt D μ [up i]) - 1 by rw [h_wt_up, h]; omega,
    bubR_eq_c, c_wt_up]

/-- The other orientation has its nonzero scalar normalization at weight -2. -/
theorem altFakeL_boundary (i : I) (μ : X) (h : D.h i μ = -2) :
    bubL cs i μ (-3) = (cs.c μ i : k) • 𝟙 _ := by
  rw [show (-3 : ℤ) = D.h i μ - 1 by omega, bubL_eq_c]

/-- The inverse-crossing component with dots, including the top degree `n=h`.
The lower cap components vanish; no annihilator hypothesis is added. -/
theorem alt_lcross_dots_sigma (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) ≤ D.h i μ) :
    cl D Sc μ [dn i, up i] [dn i, up i]
      (lcrossL i i ++ dotsL [] i [dn i] n ++ sigmaL i i) =
    -(zsign k (D.parity i * (n : ZMod 2)) •
      cl D Sc μ [dn i, up i] [dn i, up i] (dotsL [dn i] i [] n)) := by
  have e := congrArg (fun f => lcM D Sc i μ ≫ f) (lemma31_eq3_eq Sc i μ n)
  rw [Preadditive.comp_sub, Linear.comp_smul, Preadditive.comp_sum] at e
  have hz : ∀ r ∈ range n, lcM D Sc i μ ≫
      (zsign k (D.parity i * (r : ZMod 2)) •
        cl D Sc μ [up i, dn i] [dn i, up i]
          (dotsL [] i [dn i] r ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
            dotsL [dn i] i [] (n - 1 - r))) = 0 := by
    intro r hr
    rw [Linear.comp_smul, cl_capcup, ← Category.assoc, lc_eL i μ r (by
      have := mem_range.mp hr
      omega), Limits.zero_comp, smul_zero]
  have hdR : SChain [dn i, up i] (dotsL [dn i] i [] n) [dn i, up i] :=
    sChain_dotsL [dn i] i [] n
  have hdL : SChain [up i, dn i] (dotsL [] i [dn i] n) [up i, dn i] :=
    sChain_dotsL [] i [dn i] n
  rw [sum_eq_zero hz,
    ← cl_comp (sChain_sigmaL i i) hdR,
    lc_sg_assoc i μ (by omega), sub_eq_zero, zmod2_mul_self] at e
  have e' := congrArg (zsign k (D.parity i * (n : ZMod 2)) • ·) e.symm
  rw [smul_smul, zsign_mul_self', one_smul, smul_neg] at e'
  rw [cl_comp (sChain_lcrossL i i)
    (hdL.append (sChain_sigmaL i i))] at e'
  simpa only [List.append_assoc] using e'

/-- Slide at the lower crossing, so the surviving crossing is adjacent to the cap. -/
theorem alt_tau_dots_tau (i : I) (μ : X) (n : ℕ) :
    cl D Sc μ [up i, up i, dn i] [up i]
      (tauEEF i ++ dotsL [] i [up i, dn i] n ++ tauEEF i ++ [([up i], Shape.cap i, [])]) =
    ∑ s ∈ range n, zsign k (D.parity i * (s : ZMod 2)) •
      cl D Sc μ [up i, up i, dn i] [up i]
        (dotsL [up i] i [dn i] s ++ dotsL [] i [up i, dn i] (n - 1 - s) ++
          tauEEF i ++ [([up i], Shape.cap i, [])]) := by
  have hpost : SChain [up i, up i, dn i]
      (tauEEF i ++ [([up i], Shape.cap i, [])]) [up i] :=
    (sChain_tauEEF i).append (by simp [Shape.dom, Shape.cod])
  have e := congrArg
    (ctxL D Sc μ [up i, up i, dn i] [up i] [] [] [dn i]
      (tauEEF i ++ [([up i], Shape.cap i, [])]) [up i, up i] [up i, up i])
    (lemma31_eq2_eq Sc i (wt D μ [dn i]) n)
  rw [map_sub, map_smul, map_sum] at e
  simp only [map_smul, ctxL_cl μ (s := [up i, up i]) (t := [up i, up i])
    (u := []) (v := [dn i]) (pre := []) (post := tauEEF i ++ [([up i], Shape.cap i, [])])
    (show SChain [up i, up i, dn i] [] ([] ++ [up i, up i] ++ [dn i]) from rfl) hpost] at e
  simp only [List.nil_append, List.map_append, crossL, dotsL, List.map_cons,
    List.map_nil, List.map_replicate, whL, List.append_nil, List.cons_append,
    List.append_assoc] at e
  have hz : cl D Sc μ [up i, up i, dn i] [up i]
      (dotsL [up i] i [dn i] n ++ tauEEF i ++ tauEEF i ++ [([up i], Shape.cap i, [])]) = 0 := by
    have h := cl_stepL (D := D) (Sc := Sc) μ (s₀ := [up i, up i, dn i]) (t₀ := [up i])
      (dotsL [up i] i [dn i] n) [([up i], Shape.cap i, [])] [] [dn i]
      (cl_quadEq Sc i (wt D μ [dn i]))
      (sChain_dotsL [up i] i [dn i] n) (by simp [Shape.dom, Shape.cod])
      (L := dotsL [up i] i [dn i] n ++ tauEEF i ++ tauEEF i ++ [([up i], Shape.cap i, [])])
      (by simp [crossL, whL, List.append_assoc])
    simpa only [map_zero] using h
  simp only [tauEEF, dotsL, List.append_assoc, List.cons_append, List.nil_append] at hz
  rw [hz, smul_zero, sub_zero] at e
  simpa only [tauEEF, dotsL, List.append_assoc, List.cons_append, List.nil_append] using e

/-- Each dotted cap component removes the remaining leftward crossing. -/
theorem alt_cap_component (i : I) (μ : X) (s t : ℕ) (hs : (s : ℤ) ≤ D.h i μ) :
    cl D Sc μ [up i, dn i, up i] [up i]
      ((lcrossL i i).map (whL [up i] []) ++ dotsL [up i] i [dn i] s ++
        dotsL [] i [up i, dn i] t ++ tauEEF i ++ [([up i], Shape.cap i, [])]) =
    -(zsign k (D.parity i * ((t : ZMod 2) * (1 + s) + s)) •
      cl D Sc μ [up i, dn i, up i] [up i]
        ((epsL i t).map (whL [] [up i]) ++ dotsL [] i [] s)) := by
  let B := lcrossL i i ++ dotsL [] i [dn i] s
  have hB : SChain [dn i, up i] B [up i, dn i] :=
    (sChain_lcrossL i i).append (sChain_dotsL [] i [dn i] s)
  have hd : SChain [up i] (dotsL [] i [] t) [up i] := sChain_dotsL [] i [] t
  have he := cl_interchange (D := D) (Sc := Sc) (μ := μ)
    (S := [up i, dn i, up i]) (T := [up i]) []
    (tauEEF i ++ [([up i], Shape.cap i, [])]) hd hB
  have hp : parsum D B = D.parity i * (1 + s) := by
    simp only [B, parsum_append, parsum_lcrossL, parsum_dotsL, zmod2_mul_self]
    ring
  rw [hp, parsum_dotsL] at he
  have he' := congrArg (zsign k ((t : ZMod 2) * D.parity i * (D.parity i * (1 + s))) • ·) he.symm
  rw [smul_smul, zsign_mul_self', one_smul] at he'
  have hsign : (t : ZMod 2) * D.parity i * (D.parity i * (1 + s)) =
      D.parity i * ((t : ZMod 2) * (1 + s)) := by
    generalize D.parity i = p
    generalize (t : ZMod 2) = a
    generalize (s : ZMod 2) = b
    revert p a b
    decide
  rw [hsign] at he'
  have epf := cl_step (D := D) (Sc := Sc) μ
    (s₀ := [up i, dn i, up i]) (t₀ := [up i])
    (dotsL [] i [dn i, up i] t ++ B.map (whL [up i] [])) [] [] []
    (eq_2_4_a Sc i i μ).symm
    ((show SChain [up i, dn i, up i] (dotsL [] i [dn i, up i] t)
      [up i, dn i, up i] from sChain_dotsL [] i [dn i, up i] t).append
      (hB.wh [up i] [] rfl rfl)) (by rfl)
    (L := dotsL [] i [dn i, up i] t ++ B.map (whL [up i] []) ++
      tauEEF i ++ [([up i], Shape.cap i, [])])
    (L' := dotsL [] i [dn i, up i] t ++
      (B ++ sigmaL i i).map (whL [up i] []) ++ [([], Shape.cap i, [up i])])
    (by simp [List.append_assoc])
    (by simp [List.map_append, List.append_assoc])
  have en := cl_stepL (D := D) (Sc := Sc) μ
    (s₀ := [up i, dn i, up i]) (t₀ := [up i])
    (dotsL [] i [dn i, up i] t) [([], Shape.cap i, [up i])] [up i] []
    (alt_lcross_dots_sigma i (wt D μ []) s (by simpa using hs))
    (sChain_dotsL [] i [dn i, up i] t) (by simp [Shape.dom, Shape.cod])
    (L := dotsL [] i [dn i, up i] t ++
      (B ++ sigmaL i i).map (whL [up i] []) ++ [([], Shape.cap i, [up i])]) (by rfl)
  rw [map_neg, map_smul, ctxL_cl μ (s₀ := [up i, dn i, up i]) (t₀ := [up i])
    (s := [dn i, up i]) (t := [dn i, up i])
    (u := [up i]) (v := []) (sChain_dotsL [] i [dn i, up i] t)
    (show SChain ([up i] ++ [dn i, up i] ++ []) [([], Shape.cap i, [up i])] [up i] by
      simp [Shape.dom, Shape.cod])] at en
  have ec := cl_interchange (D := D) (Sc := Sc) (μ := μ)
    (S := [up i, dn i, up i]) (T := [up i]) (dotsL [] i [dn i, up i] t) []
    (s := [up i, dn i]) (s' := []) (t := [up i]) (t' := [up i])
    (A := [([], Shape.cap i, [])]) (B := dotsL [] i [] s)
    (by simp [Shape.dom, Shape.cod]) (sChain_dotsL [] i [] s)
  simp only [parsum_cons, parsum_nil, show (Shape.cap i).parity D = 0 from rfl,
    zero_add, zero_mul, zsign_zero, one_smul] at ec
  have ecn : cl D Sc μ [up i, dn i, up i] [up i]
      (dotsL [] i [dn i, up i] t ++ (dotsL [dn i] i [] s).map (whL [up i] []) ++
        [([], Shape.cap i, [up i])]) =
      cl D Sc μ [up i, dn i, up i] [up i]
        ((epsL i t).map (whL [] [up i]) ++ dotsL [] i [] s) := by
    simpa [epsL, dotsL, whL, List.append_assoc] using ec.symm
  rw [ecn] at en
  have hen : cl D Sc μ [up i, dn i, up i] [up i]
      ((lcrossL i i).map (whL [up i] []) ++ dotsL [up i] i [dn i] s ++
        dotsL [] i [up i, dn i] t ++ tauEEF i ++ [([up i], Shape.cap i, [])]) =
      zsign k (D.parity i * ((t : ZMod 2) * (1 + s))) •
      cl D Sc μ [up i, dn i, up i] [up i]
        (dotsL [] i [dn i, up i] t ++ B.map (whL [up i] []) ++
          tauEEF i ++ [([up i], Shape.cap i, [])]) := by
    simpa [B, dotsL, whL, List.append_assoc] using he'
  rw [hen, epf, en, smul_neg, smul_smul, ← zsign_add, ← mul_add]

/-- The cap component of the first correction from the inversion relation, with no
crossing left. -/
theorem altR_eps (i : I) (μ : X) (n : ℕ)
    (hn : (n : ℤ) < D.h i (wt D μ [up i])) :
    cl D Sc μ [up i, dn i, up i] [up i]
      (altR i i i ++ (epsL i n).map (whL [] [up i])) =
    -(∑ s ∈ range n, zsign k (D.parity i *
      ((s : ZMod 2) + 1 + s * ((n - 1 - s : ℕ) : ZMod 2))) •
      cl D Sc μ [up i, dn i, up i] [up i]
        ((epsL i (n - 1 - s)).map (whL [] [up i]) ++ dotsL [] i [] s)) := by
  have hp : SChain [up i, dn i, up i] ((lcrossL i i).map (whL [up i] []))
      [up i, up i, dn i] := (sChain_lcrossL i i).wh [up i] [] rfl rfl
  have hs : SChain [up i, up i, dn i] ((sigmaL i i).map (whL [up i] []))
      [up i, dn i, up i] := (sChain_sigmaL i i).wh [up i] [] rfl rfl
  have he : SChain [up i, dn i, up i] ((epsL i n).map (whL [] [up i])) [up i] :=
    (sChain_epsL i n).wh [] [up i] rfl rfl
  have e : cl D Sc μ [up i, dn i, up i] [up i]
      (altR i i i ++ (epsL i n).map (whL [] [up i])) =
      cl D Sc μ [up i, dn i, up i] [up i, up i, dn i] ((lcrossL i i).map (whL [up i] [])) ≫
      cl D Sc μ [up i, up i, dn i] [up i]
        (tauEEF i ++ (sigmaL i i).map (whL [up i] []) ++ (epsL i n).map (whL [] [up i])) := by
    rw [cl_comp hp (((sChain_tauEEF i).append hs).append he)]
    simp only [altR, crossL, tauEEF, List.append_assoc]
  rw [e, tau_sigma_epsL, alt_tau_dots_tau, Linear.comp_smul,
    Preadditive.comp_sum, smul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun s hsn => ?_
  have hs' := mem_range.mp hsn
  have hst : (s : ℤ) ≤ D.h i μ := by rw [h_wt_up] at hn; omega
  have ht : SChain [up i, up i, dn i]
      (dotsL [up i] i [dn i] s ++ dotsL [] i [up i, dn i] (n - 1 - s) ++
        tauEEF i ++ [([up i], Shape.cap i, [])]) [up i] :=
    (((show SChain [up i, up i, dn i] (dotsL [up i] i [dn i] s) [up i, up i, dn i] from
      sChain_dotsL [up i] i [dn i] s).append (sChain_dotsL [] i [up i, dn i] _)).append
      (sChain_tauEEF i)).append (by simp [Shape.dom, Shape.cod])
  rw [Linear.comp_smul, cl_comp hp ht]
  simp only [← List.append_assoc]
  rw [alt_cap_component i μ s (n - 1 - s) hst, smul_neg, smul_neg, smul_smul, smul_smul,
    ← zsign_add, ← zsign_add]
  congr 2
  have hnat : n = s + (n - 1 - s) + 1 := by omega
  have hc := congrArg (fun a : ℕ => (a : ZMod 2)) hnat
  push_cast at hc
  rw [hc]
  congr 1
  generalize D.parity i = p
  generalize (s : ZMod 2) = a
  generalize ((n - 1 - s : ℕ) : ZMod 2) = b
  revert p a b
  decide

/-- Remove every crossing from the first correction from the inversion relation before
expanding the inverse cups.
The ♦-cup and its full support are kept. -/
theorem altInvCorrectionR_crossing_free (i : I) (μ : X) :
    altInvCorrectionR cs i μ =
    -(∑ n ∈ range (D.h i (wt D μ [up i])).toNat,
      ∑ s ∈ range n, zsign k (D.parity i *
        ((s : ZMod 2) + 1 + s * ((n - 1 - s : ℕ) : ZMod 2))) •
        cl D Sc μ [up i, dn i, up i] [up i, dn i, up i]
          ((epsL i (n - 1 - s)).map (whL [] [up i]) ++ dotsL [] i [] s ++
            (dcupL i n).map (whL [] [up i]))) := by
  rw [altInvCorrectionR, ← sum_neg_distrib]
  refine sum_congr rfl fun n hn => ?_
  have hn' : (n : ℤ) < D.h i (wt D μ [up i]) := by
    have := mem_range.mp hn
    omega
  have he : SChain [up i, dn i, up i] ((epsL i n).map (whL [] [up i])) [up i] :=
    (sChain_epsL i n).wh [] [up i] rfl rfl
  have hd : SChain [up i] ((dcupL i n).map (whL [] [up i])) [up i, dn i, up i] :=
    (sChain_dcupL i n).wh [] [up i] rfl rfl
  rw [← eq_5_11 cs i _ n hn', cl_comp (sChain_epsL i n) (sChain_dcupL i n),
    ctxL_cl μ (altR_chain i i i) (show SChain ([] ++ [up i, dn i] ++ [up i]) []
      [up i, dn i, up i] from rfl)]
  simp only [List.append_nil]
  rw [List.map_append, ← List.append_assoc,
    ← cl_comp ((altR_chain i i i).append he) hd,
    altR_eps i μ n hn', Preadditive.neg_comp, Preadditive.sum_comp]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  have het : SChain [up i, dn i, up i]
      ((epsL i (n - 1 - s)).map (whL [] [up i])) [up i] :=
    (sChain_epsL i (n - 1 - s)).wh [] [up i] rfl rfl
  rw [Linear.smul_comp, cl_comp (het.append
      (show SChain [up i] (dotsL [] i [] s) [up i] from sChain_dotsL [] i [] s)) hd]

theorem alt_cup_expand (i : I) (μ : X) (n s t : ℕ)
    (hn : (n : ℤ) < D.h i (wt D μ [up i])) (hnt : n = t + s + 1) :
    cl D Sc μ [up i, dn i, up i] [up i, dn i, up i]
      ((epsL i t).map (whL [] [up i]) ++ dotsL [] i [] s ++
        (dcupL i n).map (whL [] [up i])) =
    ∑ r ∈ range (D.h i (wt D μ [up i]) - n).toNat,
      zsign k (D.parity i * ((n : ZMod 2) * s +
        ((D.h i (wt D μ [up i]) + n + r + 1 : ℤ) : ZMod 2))) •
        altTermR cs i μ r t s := by
  have he : SChain [up i, dn i, up i] ((epsL i t).map (whL [] [up i])) [up i] :=
    (sChain_epsL i t).wh [] [up i] rfl rfl
  have hd : SChain [up i] ((dcupL i n).map (whL [] [up i])) [up i, dn i, up i] :=
    (sChain_dcupL i n).wh [] [up i] rfl rfl
  have hs : SChain [up i] (dotsL [] i [] s) [up i] := sChain_dotsL [] i [] s
  have hx := cl_interchange (D := D) (Sc := Sc) (μ := μ)
    (S := [up i, dn i, up i]) (T := [up i, dn i, up i])
    ((epsL i t).map (whL [] [up i])) [] (sChain_dcupL i n) hs
  have hp : parsum D (dcupL i n) * parsum D (dotsL [] i [] s) =
      D.parity i * ((n : ZMod 2) * s) := by
    rw [parsum_dotsL]
    simp only [parsum, parity_dcupL]
    generalize D.parity i = p
    generalize (n : ZMod 2) = a
    generalize (s : ZMod 2) = b
    revert p a b
    decide
  rw [hp] at hx
  have hx' := congrArg (zsign k (D.parity i * ((n : ZMod 2) * s)) • ·) hx.symm
  rw [smul_smul, zsign_mul_self', one_smul] at hx'
  have hnorm : cl D Sc μ [up i, dn i, up i] [up i, dn i, up i]
      ((epsL i t).map (whL [] [up i]) ++ dotsL [] i [] s ++
        (dcupL i n).map (whL [] [up i])) =
      zsign k (D.parity i * ((n : ZMod 2) * s)) •
      (cl D Sc μ [up i, dn i, up i] [up i] ((epsL i t).map (whL [] [up i])) ≫
       plcL D Sc μ [] [up i] [] [up i, dn i] (dcupRHS cs i (wt D μ [up i]) n) ≫
       cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (dotsL [up i, dn i] i [] s)) := by
    rw [← eq_5_11 cs i _ n hn, plcL_cl]
    simp only [List.nil_append, List.cons_append]
    have hds : SChain [up i, dn i, up i] (dotsL [up i, dn i] i [] s)
        [up i, dn i, up i] := sChain_dotsL [up i, dn i] i [] s
    rw [cl_comp (D := D) (Sc := Sc) (μ := μ) hd hds,
      cl_comp (D := D) (Sc := Sc) (μ := μ) he (hd.append hds)]
    simpa [dotsL, whL, List.append_assoc] using hx'
  rw [hnorm, dcupRHS, map_sum, Preadditive.sum_comp, Preadditive.comp_sum, smul_sum]
  refine sum_congr rfl fun r _ => ?_
  rw [map_smul, Linear.smul_comp, Linear.comp_smul, smul_smul, ← zsign_add, ← mul_add]
  congr 1
  have hb := bubR_mem cs i (wt D μ [up i]) (-(n : ℤ) - r - 2)
  rw [closedPar_eq] at hb
  rw [plcL_comp_of_mem μ [] [up i] hb
    (comp_mem_homPar (etaP_mem cs i _) (cl_mem_homPar (sChain_dL i r) rfl)),
    plcL_comp_of_mem μ [] [up i] (etaP_mem cs i _) (cl_mem_homPar (sChain_dL i r) rfl),
    plcL_cl]
  have hidx : -(n : ℤ) - r - 2 = -(r : ℤ) - t - s - 3 := by omega
  simp only [altTermR, lbub, cupAt, hidx, Category.assoc]
  congr 3
  simp [dotsL, whL]

theorem alt_sum_reindex {A : Type*} [AddCommMonoid A] (h : ℤ)
    (f : ℕ → ℕ → ℕ → A) (hz : ∀ r t s : ℕ, h < (r : ℤ) + t + s → f r t s = 0) :
    (∑ n ∈ range (h + 2).toNat, ∑ s ∈ range n,
      ∑ r ∈ range (h + 2 - n).toNat, f r (n - 1 - s) s) =
    ∑ r ∈ range (h + 1).toNat, ∑ t ∈ range (h + 1).toNat,
      ∑ s ∈ range (h + 1).toNat, f r t s := by
  classical
  let a := (range (h + 2).toNat).sigma fun n => (range n).sigma fun _ => range (h + 2 - n).toNat
  let b := (range (h + 1).toNat) ×ˢ ((range (h + 1).toNat) ×ˢ (range (h + 1).toNat))
  have e : (∑ x ∈ a, f x.2.2 (x.1 - 1 - x.2.1) x.2.1) =
      ∑ y ∈ b, f y.1 y.2.1 y.2.2 := by
    apply sum_bij_ne_zero (fun x _ _ => (x.2.2, x.1 - 1 - x.2.1, x.2.1))
    · intro x hx _
      rcases x with ⟨n, s, r⟩
      simp only [a, mem_sigma, mem_range] at hx
      simp only [b, mem_product, mem_range]
      omega
    · intro x hx _ y hy _ heq
      rcases x with ⟨n, s, r⟩
      rcases y with ⟨n', s', r'⟩
      simp only [a, mem_sigma, mem_range] at hx hy
      simp only [Prod.mk.injEq] at heq
      have : n = n' := by omega
      obtain ⟨rfl, hts, rfl⟩ := heq
      subst n'
      rfl
    · intro y hy hnz
      rcases y with ⟨r, t, s⟩
      have hle : (r : ℤ) + t + s ≤ h := by
        by_contra hn
        exact hnz (hz r t s (by omega))
      have hm : (⟨t + s + 1, ⟨s, r⟩⟩ : Σ _ : ℕ, Σ _ : ℕ, ℕ) ∈ a := by
        simp only [a, mem_sigma, mem_range]
        omega
      refine ⟨⟨t + s + 1, ⟨s, r⟩⟩, hm, ?_, ?_⟩
      · simpa only [show t + s + 1 - 1 - s = t by omega] using hnz
      · simp only [show t + s + 1 - 1 - s = t by omega]
    · intro x _ _
      rfl
  simpa only [a, b, sum_sigma', sum_product] using e

theorem altInvCorrectionR_eq (i : I) (μ : X) :
    altInvCorrectionR cs i μ = -altCorrectionR cs i μ := by
  rw [altInvCorrectionR_crossing_free]
  congr 1
  calc
    _ = ∑ n ∈ range (D.h i μ + 2).toNat, ∑ s ∈ range n,
        ∑ r ∈ range (D.h i μ + 2 - n).toNat,
          isg k (D.parity i) (D.h i μ + r + (n - 1 - s : ℕ) + 1) •
            altTermR cs i μ r (n - 1 - s) s := by
      rw [h_wt_up]
      refine sum_congr rfl fun n hn => sum_congr rfl fun s hs => ?_
      have hn' : (n : ℤ) < D.h i (wt D μ [up i]) := by
        rw [h_wt_up]; simp only [mem_range] at hn; omega
      have hnt : n = (n - 1 - s) + s + 1 := by simp only [mem_range] at hs; omega
      rw [alt_cup_expand cs i μ n s (n - 1 - s) hn' hnt, smul_sum, h_wt_up]
      refine sum_congr rfl fun r _ => ?_
      rw [smul_smul, ← zsign_add, isg]
      congr 2
      have hc := congrArg (fun a : ℕ => (a : ZMod 2)) hnt
      push_cast at hc ⊢
      rw [hc]
      generalize D.parity i = p
      generalize (D.h i μ : ZMod 2) = h
      generalize ((n - 1 - s : ℕ) : ZMod 2) = t
      generalize (s : ZMod 2) = a
      generalize (r : ZMod 2) = b
      revert p h t a b
      decide
    _ = altCorrectionR cs i μ := by
      exact alt_sum_reindex (D.h i μ)
        (fun r t s => isg k (D.parity i) (D.h i μ + r + t + 1) • altTermR cs i μ r t s)
        (fun r t s h => by rw [altTermR_vanish cs i μ r t s h, smul_zero])

theorem alt_sigma_dots_lcross (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) ≤ -D.h i μ) :
    cl D Sc μ [up i, dn i] [up i, dn i]
      (sigmaL i i ++ dotsL [dn i] i [] n ++ lcrossL i i) =
    -(zsign k (D.parity i * (n : ZMod 2)) •
      cl D Sc μ [up i, dn i] [up i, dn i] (dotsL [] i [dn i] n)) := by
  have e := congrArg (fun f => f ≫ lcM D Sc i μ) (lemma31_eq3_eq Sc i μ n)
  rw [Preadditive.sub_comp, Linear.smul_comp, Preadditive.sum_comp] at e
  have hz : ∀ r ∈ range n,
      (zsign k (D.parity i * (r : ZMod 2)) •
        cl D Sc μ [up i, dn i] [dn i, up i]
          (dotsL [] i [dn i] r ++ [([], Shape.cap i, []), ([], Shape.cup i, [])] ++
            dotsL [dn i] i [] (n - 1 - r))) ≫ lcM D Sc i μ = 0 := by
    intro r hr
    rw [Linear.smul_comp, cl_capcup, Category.assoc,
      cl_comp (sChain_etaL i (n - 1 - r)) (sChain_lcrossL i i),
      cl_invM₃ Sc i μ (n - 1 - r) (by have := mem_range.mp hr; omega),
      Limits.comp_zero, smul_zero]
  rw [sum_eq_zero hz, ← cl_comp (sChain_dL i n) (sChain_sigmaL i i),
    Category.assoc, sg_lc_nonpos i μ (by omega), Preadditive.comp_neg,
    Category.comp_id, smul_neg, sub_neg_eq_add, add_eq_zero_iff_eq_neg, zmod2_mul_self] at e
  rw [cl_comp ((sChain_sigmaL i i).append (sChain_dR i n)) (sChain_lcrossL i i)] at e
  exact e

theorem alt_tau_dotsR_tau (i : I) (μ : X) (n : ℕ) :
    cl D Sc μ [up i, up i] [up i, up i]
      (crossL [] i i [] ++ dotsL [up i] i [] n ++ crossL [] i i []) =
    -(zsign k (D.parity i * (n : ZMod 2)) •
      ∑ s ∈ range n, zsign k (D.parity i * (s : ZMod 2)) •
        cl D Sc μ [up i, up i] [up i, up i]
          (crossL [] i i [] ++ dotsL [up i] i [] s ++ dotsL [] i [up i] (n - 1 - s))) := by
  have ht : SChain [up i, up i] (crossL [] i i []) [up i, up i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have e := lemma31_eq2_eq Sc i μ n
  rw [zmod2_mul_self] at e
  have e' : cl D Sc μ [up i, up i] [up i, up i]
      (dotsL [up i] i [] n ++ crossL [] i i []) =
      zsign k (D.parity i * (n : ZMod 2)) •
      (cl D Sc μ [up i, up i] [up i, up i] (crossL [] i i [] ++ dotsL [] i [up i] n) -
       ∑ s ∈ range n, zsign k (D.parity i * (s : ZMod 2)) •
        cl D Sc μ [up i, up i] [up i, up i]
          (dotsL [up i] i [] s ++ dotsL [] i [up i] (n - 1 - s))) := by
    rw [← e, sub_sub_cancel, smul_smul, zsign_mul_self', one_smul]
  have hdl : SChain [up i, up i] (dotsL [] i [up i] n) [up i, up i] := sChain_dotsL [] i [up i] n
  rw [List.append_assoc, ← cl_comp ht ((sChain_dotsL [up i] i [] n).append ht), e',
    Linear.comp_smul, Preadditive.comp_sub,
    ← cl_comp (D := D) (Sc := Sc) (μ := μ) ht hdl, ← Category.assoc,
    cl_comp ht ht, cl_quadEq, Limits.zero_comp, zero_sub, smul_neg, Preadditive.comp_sum]
  congr 2
  refine sum_congr rfl fun s _ => ?_
  have hds : SChain [up i, up i]
      (dotsL [up i] i [] s ++ dotsL [] i [up i] (n - 1 - s)) [up i, up i] :=
    (sChain_dotsL [up i] i [] s).append (sChain_dotsL [] i [up i] _)
  rw [Linear.comp_smul, cl_comp (D := D) (Sc := Sc) (μ := μ) ht hds]
  simp only [List.append_assoc]

theorem alt_eta_crossFE (i : I) (μ : X) (n : ℕ) :
    cl D Sc μ [up i] [dn i, up i, up i]
      ((etaL i n).map (whL [up i] []) ++ crossFE i) =
    -(∑ s ∈ range n, zsign k (D.parity i * (s : ZMod 2)) •
      cl D Sc μ [up i] [dn i, up i, up i]
        ([([], Shape.cup i, [up i])] ++
          (crossL [] i i [] ++ dotsL [up i] i [] s ++ dotsL [] i [up i] (n - 1 - s)).map
            (whL [dn i] []))) := by
  have ht : SChain [up i, up i] (crossL [] i i []) [up i, up i] := by
    simp [crossL, Shape.dom, Shape.cod]
  have e := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := [up i]) (T := [dn i, up i, up i])
    [([up i], Shape.cup i, [])] [([dn i], Shape.cross i i, [])]
    (sChain_sigmaL i i) (sChain_dotsL [] i [] n)
  rw [parsum_sigmaL, parsum_dotsL] at e
  have e' := congrArg (zsign k (D.parity i * D.parity i * ((n : ZMod 2) * D.parity i)) • ·) e
  rw [smul_smul, zsign_mul_self', one_smul] at e'
  have epf := cl_step (D := D) (Sc := Sc) μ (s₀ := [up i]) (t₀ := [dn i, up i, up i])
    [] (dotsL [dn i, up i] i [] n ++ [([dn i], Shape.cross i i, [])]) [] []
    (eq_2_4_b Sc i i μ) (by rfl)
    ((sChain_dotsL [dn i, up i] i [] n).append (ht.wh [dn i] [] rfl rfl))
    (L := [([up i], Shape.cup i, [])] ++ (sigmaL i i).map (whL [] [up i]) ++
      dotsL [dn i, up i] i [] n ++ [([dn i], Shape.cross i i, [])])
    (L' := [([], Shape.cup i, [up i])] ++
      (crossL [] i i [] ++ dotsL [up i] i [] n ++ crossL [] i i []).map (whL [dn i] []))
    (by simp [List.append_assoc]) (by simp [crossL, dotsL, whL])
  have en : cl D Sc μ [up i] [dn i, up i, up i]
      ((etaL i n).map (whL [up i] []) ++ crossFE i) =
      zsign k (D.parity i * (n : ZMod 2)) •
      cl D Sc μ [up i] [dn i, up i, up i]
        ([([], Shape.cup i, [up i])] ++
          (crossL [] i i [] ++ dotsL [up i] i [] n ++ crossL [] i i []).map (whL [dn i] [])) := by
    rw [← epf]
    have hp : D.parity i * D.parity i * ((n : ZMod 2) * D.parity i) =
        D.parity i * (n : ZMod 2) := by
      generalize D.parity i = p; generalize (n : ZMod 2) = a
      revert p a; decide
    rw [hp] at e'
    simpa [etaL, crossFE, dotsL, whL, List.append_assoc] using e'.symm
  have ee := cl_stepL (D := D) (Sc := Sc) μ (s₀ := [up i]) (t₀ := [dn i, up i, up i])
    [([], Shape.cup i, [up i])] [] [dn i] [] (alt_tau_dotsR_tau i (wt D μ []) n)
    (by simp [Shape.dom, Shape.cod]) (by rfl)
    (L := [([], Shape.cup i, [up i])] ++
      (crossL [] i i [] ++ dotsL [up i] i [] n ++ crossL [] i i []).map (whL [dn i] [])) (by simp)
  rw [en, ee, map_neg, map_smul, map_sum, smul_neg, smul_smul, zsign_mul_self', one_smul]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  rw [map_smul, ctxL_cl μ (by simp [Shape.dom, Shape.cod]) (by rfl)]
  simp only [List.append_nil]

theorem alt_cup_component (i : I) (μ : X) (s t : ℕ)
    (ht : (t : ℤ) ≤ -D.h i (wt D μ [up i])) :
    cl D Sc μ [up i] [up i, dn i, up i]
      ([([], Shape.cup i, [up i])] ++ crossL [dn i] i i [] ++
        dotsL [dn i, up i] i [] s ++ dotsL [dn i] i [up i] t ++
        (lcrossL i i).map (whL [] [up i])) =
    -(zsign k (D.parity i * ((s : ZMod 2) + t)) •
      cl D Sc μ [up i] [up i, dn i, up i]
        ((etaL i s).map (whL [up i] []) ++ dotsL [] i [dn i, up i] t)) := by
  let B := dotsL [dn i] i [] t ++ lcrossL i i
  have hB : SChain [dn i, up i] B [up i, dn i] :=
    (sChain_dR i t).append (sChain_lcrossL i i)
  have hd : SChain [up i] (dotsL [] i [] s) [up i] := sChain_dotsL [] i [] s
  have ex := cl_interchange (D := D) (Sc := Sc) (μ := μ)
    (S := [up i]) (T := [up i, dn i, up i])
    ([([], Shape.cup i, [up i])] ++ crossL [dn i] i i []) [] hB hd
  have hp : parsum D B * parsum D (dotsL [] i [] s) =
      D.parity i * ((s : ZMod 2) * (t + 1)) := by
    simp only [B, parsum_append, parsum_dotsL, parsum_lcrossL, zmod2_mul_self]
    generalize D.parity i = p; generalize (s : ZMod 2) = a; generalize (t : ZMod 2) = b
    revert p a b; decide
  rw [hp] at ex
  have ex' := congrArg (zsign k (D.parity i * ((s : ZMod 2) * (t + 1))) • ·) ex.symm
  rw [smul_smul, zsign_mul_self', one_smul] at ex'
  have en : cl D Sc μ [up i] [up i, dn i, up i]
      ([([], Shape.cup i, [up i])] ++ crossL [dn i] i i [] ++
        dotsL [dn i, up i] i [] s ++ dotsL [dn i] i [up i] t ++
        (lcrossL i i).map (whL [] [up i])) =
      zsign k (D.parity i * ((s : ZMod 2) * (t + 1))) •
      cl D Sc μ [up i] [up i, dn i, up i]
        ([([], Shape.cup i, [up i])] ++ crossL [dn i] i i [] ++
          B.map (whL [] [up i]) ++ dotsL [up i, dn i] i [] s) := by
    simpa [B, dotsL, whL, List.append_assoc] using ex'
  have epf := cl_step (D := D) (Sc := Sc) μ (s₀ := [up i]) (t₀ := [up i, dn i, up i])
    [] (B.map (whL [] [up i]) ++ dotsL [up i, dn i] i [] s) [] []
    (eq_2_4_b Sc i i μ).symm (by rfl)
    ((hB.wh [] [up i] rfl rfl).append (sChain_dotsL [up i, dn i] i [] s))
    (L := [([], Shape.cup i, [up i])] ++ crossL [dn i] i i [] ++
      B.map (whL [] [up i]) ++ dotsL [up i, dn i] i [] s)
    (L' := [([up i], Shape.cup i, [])] ++
      (sigmaL i i ++ B).map (whL [] [up i]) ++ dotsL [up i, dn i] i [] s)
    (by simp [crossL]) (by simp [List.map_append, List.append_assoc])
  have ei := cl_stepL (D := D) (Sc := Sc) μ (s₀ := [up i]) (t₀ := [up i, dn i, up i])
    [([up i], Shape.cup i, [])] (dotsL [up i, dn i] i [] s) [] [up i]
    (alt_sigma_dots_lcross i (wt D μ [up i]) t ht)
    (by simp [Shape.dom, Shape.cod]) (sChain_dotsL [up i, dn i] i [] s)
    (L := [([up i], Shape.cup i, [])] ++
      (sigmaL i i ++ B).map (whL [] [up i]) ++ dotsL [up i, dn i] i [] s)
    (by simp [B, List.append_assoc])
  rw [map_neg, map_smul, ctxL_cl μ (s₀ := [up i]) (t₀ := [up i, dn i, up i])
    (s := [up i, dn i]) (t := [up i, dn i]) (u := []) (v := [up i])
    (by simp [Shape.dom, Shape.cod])
    (show SChain ([] ++ [up i, dn i] ++ [up i]) (dotsL [up i, dn i] i [] s)
      [up i, dn i, up i] from sChain_dotsL [up i, dn i] i [] s)] at ei
  have ed := cl_interchange (D := D) (Sc := Sc) (μ := μ)
    (S := [up i]) (T := [up i, dn i, up i]) [([up i], Shape.cup i, [])] []
    (sChain_dotsL [] i [] t) (sChain_dR i s)
  rw [parsum_dotsL, parsum_dotsL] at ed
  have ep : (t : ZMod 2) * D.parity i * ((s : ZMod 2) * D.parity i) =
      D.parity i * ((s : ZMod 2) * t) := by
    generalize D.parity i = p; generalize (s : ZMod 2) = a; generalize (t : ZMod 2) = b
    revert p a b; decide
  rw [ep] at ed
  have ed' : cl D Sc μ [up i] [up i, dn i, up i]
      ([([up i], Shape.cup i, [])] ++ (dotsL [] i [dn i] t).map (whL [] [up i]) ++
        dotsL [up i, dn i] i [] s) =
      zsign k (D.parity i * ((s : ZMod 2) * t)) •
      cl D Sc μ [up i] [up i, dn i, up i]
        ((etaL i s).map (whL [up i] []) ++ dotsL [] i [dn i, up i] t) := by
    simpa [etaL, dotsL, whL, List.append_assoc] using ed
  rw [en, epf, ei, ed', smul_neg, smul_smul, smul_smul, ← zsign_add, ← zsign_add]
  congr 3
  generalize D.parity i = p; generalize (s : ZMod 2) = a; generalize (t : ZMod 2) = b
  revert p a b; decide

theorem alt_eta_altL (i : I) (μ : X) (n : ℕ) (hn : (n : ℤ) < -D.h i μ) :
    cl D Sc μ [up i] [up i, dn i, up i]
      ((etaL i n).map (whL [up i] []) ++ altL i i i) =
    ∑ s ∈ range n, zsign k (D.parity i * ((n - 1 - s : ℕ) : ZMod 2)) •
      cl D Sc μ [up i] [up i, dn i, up i]
        ((etaL i s).map (whL [up i] []) ++ dotsL [] i [dn i, up i] (n - 1 - s)) := by
  have he : SChain [up i] ((etaL i n).map (whL [up i] [])) [up i, dn i, up i] :=
    (sChain_etaL i n).wh [up i] [] rfl rfl
  have hc : SChain [dn i, up i, up i] ((lcrossL i i).map (whL [] [up i])) [up i, dn i, up i] :=
    (sChain_lcrossL i i).wh [] [up i] rfl rfl
  have en : (etaL i n).map (whL [up i] []) ++ altL i i i =
      ((etaL i n).map (whL [up i] []) ++ crossFE i) ++ (lcrossL i i).map (whL [] [up i]) := by
    simp [altL, crossFE, crossL, List.append_assoc]
  rw [en, ← cl_comp (he.append (sChain_crossFE i)) hc,
    alt_eta_crossFE, Preadditive.neg_comp, Preadditive.sum_comp, ← sum_neg_distrib]
  refine sum_congr rfl fun s hs => ?_
  have ht : (n - 1 - s : ℕ) ≤ -D.h i (wt D μ [up i]) := by
    have := mem_range.mp hs
    rw [h_wt_up]
    omega
  have hchain : SChain [up i]
      ([([], Shape.cup i, [up i])] ++
        (crossL [] i i [] ++ dotsL [up i] i [] s ++ dotsL [] i [up i] (n - 1 - s)).map
          (whL [dn i] [])) [dn i, up i, up i] :=
    (show SChain [up i] [([], Shape.cup i, [up i])] [dn i, up i, up i] by
      simp [Shape.dom, Shape.cod]).append
      (((show SChain [up i, up i] (crossL [] i i []) [up i, up i] by
        simp [crossL, Shape.dom, Shape.cod]).append
        (sChain_dotsL [up i] i [] s) |>.append
          (sChain_dotsL [] i [up i] (n - 1 - s))).wh [dn i] [] rfl rfl)
  rw [Linear.smul_comp, cl_comp hchain hc]
  have ed : [([], Shape.cup i, [up i])] ++
      (crossL [] i i [] ++ dotsL [up i] i [] s ++ dotsL [] i [up i] (n - 1 - s)).map
        (whL [dn i] []) ++ (lcrossL i i).map (whL [] [up i]) =
      [([], Shape.cup i, [up i])] ++ crossL [dn i] i i [] ++
        dotsL [dn i, up i] i [] s ++ dotsL [dn i] i [up i] (n - 1 - s) ++
        (lcrossL i i).map (whL [] [up i]) := by simp [crossL, dotsL, whL]
  rw [ed, alt_cup_component i μ s (n - 1 - s) ht, smul_neg, neg_neg,
    smul_smul, ← zsign_add]
  congr 2
  generalize D.parity i = p; generalize (s : ZMod 2) = a
  generalize ((n - 1 - s : ℕ) : ZMod 2) = b
  revert p a b; decide

theorem altInvCorrectionL_crossing_free (i : I) (μ : X) :
    altInvCorrectionL cs i μ =
      ∑ n ∈ range (-D.h i μ).toNat, ∑ s ∈ range n,
        zsign k (D.parity i * ((n - 1 - s : ℕ) : ZMod 2)) •
          (plcL D Sc μ [up i] [] [dn i, up i] [] (dcapRHS cs i (wt D μ []) n) ≫
            cl D Sc μ [up i] [up i, dn i, up i]
              ((etaL i s).map (whL [up i] []) ++ dotsL [] i [dn i, up i] (n - 1 - s))) := by
  rw [altInvCorrectionL]
  refine sum_congr rfl fun n hn => ?_
  have hn' : (n : ℤ) < -D.h i μ := by have := mem_range.mp hn; omega
  simp only [ctxL, LinearMap.coe_mk, AddHom.coe_mk, List.cons_append, List.nil_append,
    cl_nil, Category.id_comp]
  change plcL D Sc μ [up i] [] [dn i, up i] [dn i, up i]
      (dcapRHS cs i (wt D μ []) n ≫ cl D Sc (wt D μ []) [] [dn i, up i] (etaL i n)) ≫
      cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (altL i i i) = _
  have hn'' : (n : ℤ) < -D.h i (wt D μ []) := hn'
  rw [← eq_5_12 cs i _ n hn'',
    plcL_comp_of_mem μ [up i] [] (cl_mem_homPar (sChain_dcapL i n) rfl) (etaL_mem i _ n),
    plcL_cl, plcL_cl, Category.assoc]
  simp only [List.cons_append, List.nil_append]
  have he : SChain [up i] ((etaL i n).map (whL [up i] [])) [up i, dn i, up i] :=
    (sChain_etaL i n).wh [up i] [] rfl rfl
  rw [cl_comp (D := D) (Sc := Sc) (μ := μ) he (altL_chain i i i),
    alt_eta_altL i μ n hn', Preadditive.comp_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [Linear.comp_smul]
  congr 2
  exact (plcL_cl (D := D) (Sc := Sc) μ [up i] [] [dn i, up i] [] (dcapL i n)).symm

theorem alt_cap_expand (i : I) (μ : X) (n s t : ℕ) (hnt : n = t + s + 1) :
    plcL D Sc μ [up i] [] [dn i, up i] [] (dcapRHS cs i (wt D μ []) n) ≫
      cl D Sc μ [up i] [up i, dn i, up i]
        ((etaL i s).map (whL [up i] []) ++ dotsL [] i [dn i, up i] t) =
    ∑ r ∈ range (-D.h i μ - n).toNat,
      isg k (D.parity i) (D.h i μ + n + r + 1) • altTermL cs i μ r s t := by
  rw [dcapRHS, map_sum, Preadditive.sum_comp]
  refine sum_congr (by rfl) fun r _ => ?_
  rw [map_smul, Linear.smul_comp]
  congr 1
  have hb := bubL_mem cs i (wt D μ []) (-(n : ℤ) - r - 2)
  rw [closedPar_eq] at hb
  rw [plcL_comp_of_mem μ [up i] [] (cl_mem_homPar (sChain_dR i r) rfl)
    (comp_mem_homPar (epsP_mem cs i _) hb),
    plcL_comp_of_mem μ [up i] [] (epsP_mem cs i _) hb, plcL_cl]
  have he : SChain [up i] ((etaL i s).map (whL [up i] [])) [up i, dn i, up i] :=
    (sChain_etaL i s).wh [up i] [] rfl rfl
  have hd : SChain [up i, dn i, up i] (dotsL [] i [dn i, up i] t) [up i, dn i, up i] :=
    sChain_dotsL [] i [dn i, up i] t
  rw [← cl_comp he hd]
  have hi : -(n : ℤ) - r - 2 = -(r : ℤ) - s - t - 3 := by omega
  simp only [altTermL, rbub, capAt, wt_nil, hi, Category.assoc]
  congr 1
  simp [dotsL, whL]

/-- The second triple sum of [BE2] Prop 7.6 with the sign of ERRATA [BE2] 2:
exponent `pᵢ(hᵢ(μ) + r + s)`, without the spectator dots. -/
def altCorrectionL (i : I) (μ : X) :
    (pres D Sc).obj (ob D μ [up i, dn i, up i]) ⟶ (pres D Sc).obj (ob D μ [up i, dn i, up i]) :=
  ∑ r ∈ range (-D.h i μ - 1).toNat, ∑ s ∈ range (-D.h i μ - 1).toNat,
    ∑ t ∈ range (-D.h i μ - 1).toNat,
      isg k (D.parity i) (D.h i μ + r + s) • altTermL cs i μ r s t

theorem altInvCorrectionL_eq (i : I) (μ : X) :
    altInvCorrectionL cs i μ = altCorrectionL cs i μ := by
  rw [altInvCorrectionL_crossing_free]
  calc
    _ = ∑ n ∈ range (-D.h i μ).toNat, ∑ s ∈ range n,
        ∑ r ∈ range (-D.h i μ - n).toNat,
          isg k (D.parity i) (D.h i μ + r + s) • altTermL cs i μ r s (n - 1 - s) := by
      refine sum_congr rfl fun n _ => sum_congr rfl fun s hs => ?_
      have hn : n = (n - 1 - s) + s + 1 := by have := mem_range.mp hs; omega
      rw [alt_cap_expand cs i μ n s (n - 1 - s) hn, smul_sum]
      refine sum_congr rfl fun r _ => ?_
      rw [smul_smul, isg, ← zsign_add]
      congr 2
      have hc := congrArg (fun a : ℕ => (a : ZMod 2)) hn
      push_cast at hc ⊢
      rw [hc]
      generalize D.parity i = p; generalize (D.h i μ : ZMod 2) = h
      generalize ((n - 1 - s : ℕ) : ZMod 2) = t
      generalize (s : ZMod 2) = a; generalize (r : ZMod 2) = b
      revert p h t a b; decide
    _ = altCorrectionL cs i μ := by
      have e := alt_sum_reindex (-D.h i μ - 2)
        (fun r t s => isg k (D.parity i) (D.h i μ + r + s) • altTermL cs i μ r s t)
        (fun r t s h => by rw [altTermL_vanish cs i μ r s t (by omega), smul_zero])
      rw [show -D.h i μ - 2 + 2 = -D.h i μ by omega,
        show -D.h i μ - 2 + 1 = -D.h i μ - 1 by omega] at e
      rw [e, altCorrectionL]
      refine sum_congr rfl fun r _ => ?_
      rw [sum_comm]

/-- [BE2] Prop 7.6 for `i = j = k`, with the sign of ERRATA [BE2] 2 in the second sum. -/
theorem alt_equal (i : I) (μ : X) :
    cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (altL i i i) =
      cl D Sc μ [up i, dn i, up i] [up i, dn i, up i] (altR i i i) +
        altCorrectionR cs i μ + altCorrectionL cs i μ := by
  have e := alt_equal_inv cs i μ
  rw [altInvCorrectionR_eq, altInvCorrectionL_eq, sub_neg_eq_add] at e
  rw [sub_eq_iff_eq_add] at e
  exact e.trans (by abel)


theorem altInvCorrectionR_boundary (i : I) (μ : X) (hh : D.h i μ = -1) :
    altInvCorrectionR cs i μ = 0 := by
  rw [altInvCorrectionR_eq, altCorrectionR_boundary cs i μ hh, neg_zero]

theorem altInvCorrectionL_boundary (i : I) (μ : X) (hh : D.h i μ = -1) :
    altInvCorrectionL cs i μ = 0 := by
  rw [altInvCorrectionL_eq]
  simp [altCorrectionL, hh]

theorem altInvCorrectionR_at_zero (i : I) (μ : X) (hh : D.h i μ = 0) :
    altInvCorrectionR cs i μ = -(isg k (D.parity i) 1 • altTermR cs i μ 0 0 0) := by
  rw [altInvCorrectionR_eq]
  simp [altCorrectionR, hh]

theorem altInvCorrectionL_at_neg_two (i : I) (μ : X) (hh : D.h i μ = -2) :
    altInvCorrectionL cs i μ = altTermL cs i μ 0 0 0 := by
  rw [altInvCorrectionL_eq]
  norm_num [altCorrectionL, hh, isg]
  change zsign k (D.parity i * (0 : ZMod 2)) • _ = _
  rw [mul_zero, zsign_zero, one_smul]

end OddMath.SKM
