/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PsiAdjunctions
import OddMath.SKM.Cyclicity

/-!
# The mixed crossing and distinct-colour inversion for ψ

`psiMixed_inversion` proves the distinct-colour inversion requirement (1.12)
for the actual whiskered images of the printed assignments in the proof of
Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 9.4. This supplies the mixed-crossing and distinct-colour
inverse-generator checks needed to descend ψ to the presented category.

`psiSigma_eq_composite` evaluates (1.11) using the assigned cup, upward crossing,
and cap, the downward parity shift, and the actual target whiskerings.
`psi_invNe₁` and `psi_invNe₂` are its two normalized inverse equations.
The mixed crossing and inverse images have the source parity and degree zero.

These equations hold over a commutative ring with `t² = -1`, rather than only
the field used in §9; the composite calculation additionally uses `CScalars`.
They do not establish the same-colour matrix inversion checks (1.13)–(1.14),
the strict graded functor, its envelope extension, or a categorical isomorphism.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

private theorem wt_mixed (μ : X) (i j : I) :
    wt D μ [dn i, up j] = wt D μ [up j, dn i] := by
  simp only [wt_cons, wt_nil]
  simp [sh, add_left_comm, add_comm, add_assoc]

private theorem ipar_root (μ : X) (i j : I) :
    ipar D i (wt D μ [up j]) = ipar D i μ := by
  rw [ipar, ipar, h_wt_upj]
  push_cast
  have h : D.parity i * (D.d i j : ZMod 2) = 0 := by
    by_cases hi : D.parity i = 1
    · obtain ⟨n, hn⟩ := D.even_d_of_odd hi j
      rw [hn]
      push_cast
      rw [mul_add, ← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
    · rw [zmod2_eq_zero_of_ne_one hi, zero_mul]
  linear_combination -h

private theorem mixed_parity (μ : X) (i j : I) :
    psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc)
      (wt D μ [up j, dn i]) μ [dn i, up j] (wt_mixed μ i j)) = ipar D i μ := by
  simpa [psiParity, psiWordAt, ob, wd] using ipar_root μ i j

/-- The normalized image of the mixed crossing. -/
def psiSigma (t : k) (μ : X) (i j : I) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [up j, dn i]) μ [up j, dn i] rfl ⟶
      psiAt (wt D μ [up j, dn i]) μ [dn i, up j] (wt_mixed μ i j) :=
  SOp.mk' ((psiCoeff t (D.parity i * D.parity j) *
    sign k (D.parity i * D.parity j * ipar D i μ)) •
      cl D Sc μ [dn i, up j] [up j, dn i] (lcrossL i j))

/-- The candidate image of the inverse crossing. -/
def psiLCross (t : k) (μ : X) (i j : I) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [up j, dn i]) μ [dn i, up j] (wt_mixed μ i j) ⟶
      psiAt (wt D μ [up j, dn i]) μ [up j, dn i] rfl :=
  SOp.mk' ((psiCoeff t (D.parity i * D.parity j) *
    sign k (D.parity i * D.parity j * ipar D i μ)) •
      cl D Sc μ [up j, dn i] [dn i, up j] (sigmaL i j))

private theorem psiSigmaRaw_mem (μ : X) (i j : I) :
    (show SOp.unop (psiAt (Sc := Sc) (sy := sy) (hc := hc)
        (wt D μ [up j, dn i]) μ [up j, dn i] rfl) ⟶
      SOp.unop (psiAt (wt D μ [up j, dn i]) μ [dn i, up j] (wt_mixed μ i j)) from
        cl D Sc μ [up j, dn i] [dn i, up j] (sigmaL i j)) ∈
      parity (R := k) _ _ (D.parity i * D.parity j) := by
  change _ ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _
    (D.parity i * D.parity j + (psiParity (sy := sy) (hc := hc)
      (psiWordAt (Sc := Sc) (wt D μ [up j, dn i]) μ [up j, dn i] rfl) +
      psiParity (sy := sy) (hc := hc)
      (psiWordAt (Sc := Sc) (wt D μ [up j, dn i]) μ [dn i, up j] (wt_mixed μ i j))))
  rw [mixed_parity]
  have hp : psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc)
      (wt D μ [up j, dn i]) μ [up j, dn i] rfl) = ipar D i μ := by
    simp [psiParity, psiWordAt, ob, wd]
  rw [hp, zmod2_add_self, add_zero, cl_of (sChain_sigmaL i j)]
  apply Presentation.diag_mem_homDeg'
  rw [degree_parity_mkD, parity_sigmaL]

private theorem lcross_mem (μ : X) (i j : I) :
    (show SOp.unop (psiAt (Sc := Sc) (sy := sy) (hc := hc)
        (wt D μ [up j, dn i]) μ [dn i, up j] (wt_mixed μ i j)) ⟶
      SOp.unop (psiAt (wt D μ [up j, dn i]) μ [up j, dn i] rfl) from
        cl D Sc μ [dn i, up j] [up j, dn i] (lcrossL i j)) ∈
      parity (R := k) _ _ (D.parity i * D.parity j) := by
  change _ ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _
    (D.parity i * D.parity j + (psiParity (sy := sy) (hc := hc)
      (psiWordAt (Sc := Sc) (wt D μ [up j, dn i]) μ [dn i, up j] (wt_mixed μ i j)) +
      psiParity (sy := sy) (hc := hc)
      (psiWordAt (Sc := Sc) (wt D μ [up j, dn i]) μ [up j, dn i] rfl)))
  rw [mixed_parity]
  have hp : psiParity (sy := sy) (hc := hc) (psiWordAt (Sc := Sc)
      (wt D μ [up j, dn i]) μ [up j, dn i] rfl) = ipar D i μ := by
    simp [psiParity, psiWordAt, ob, wd]
  rw [hp, zmod2_add_self, add_zero, cl_of (sChain_lcrossL i j)]
  apply Presentation.diag_mem_homDeg'
  rw [degree_parity_mkD, parity_lcrossL]

private theorem mixed_coeff (t : k) (ht : t ^ 2 = -1) (p a : ZMod 2) :
    sign k (p * p) * ((psiCoeff t p * sign k (p * a)) *
      (psiCoeff t p * sign k (p * a))) = 1 := by
  have h := psiCoeff_comp ht p p
  have hp : p + p = 0 := zmod2_add_self p
  rw [hp, psiCoeff_zero] at h
  calc
    _ = (sign k (p * p) * (psiCoeff t p * psiCoeff t p)) *
      (sign k (p * a) * sign k (p * a)) := by ring
    _ = 1 := by rw [h, sign_mul_self, mul_one]

/-- The first distinct-colour inverse equation of (1.12). -/
theorem psi_invNe₁ (t : k) (ht : t ^ 2 = -1) (μ : X) (i j : I) (hij : i ≠ j) :
    psiSigma (Sc := Sc) (sy := sy) (hc := hc) t μ i j ≫ psiLCross t μ i j = 𝟙 _ := by
  apply SOp.hom_ext
  unfold psiSigma psiLCross
  rw [SOp.unsop_comp]
  simp only [SOp.unsop_mk', SOp.smul_compC, SOp.compC_smul]
  rw [SOp.compC_of_mem (lcross_mem (Sc := Sc) (sy := sy) (hc := hc) μ i j)
    (psiSigmaRaw_mem (Sc := Sc) (sy := sy) (hc := hc) μ i j)]
  change _ • (_ • (_ • (cl D Sc μ [up j, dn i] [dn i, up j] (sigmaL i j) ≫
    cl D Sc μ [dn i, up j] [up j, dn i] (lcrossL i j)))) = 𝟙 _
  rw [smul_smul, smul_smul,
    show _ * _ * sign k (D.parity i * D.parity j * (D.parity i * D.parity j)) = 1 from
      (mul_comm _ _).trans (mixed_coeff t ht _ _), one_smul, cl_comp (sChain_sigmaL i j) (sChain_lcrossL i j),
    cl_invNe₁ Sc i j μ hij, cl_nil]
  rfl

/-- The second distinct-colour inverse equation of (1.12). -/
theorem psi_invNe₂ (t : k) (ht : t ^ 2 = -1) (μ : X) (i j : I) (hij : i ≠ j) :
    psiLCross (Sc := Sc) (sy := sy) (hc := hc) t μ i j ≫ psiSigma t μ i j = 𝟙 _ := by
  apply SOp.hom_ext
  unfold psiSigma psiLCross
  rw [SOp.unsop_comp]
  simp only [SOp.unsop_mk', SOp.smul_compC, SOp.compC_smul]
  rw [SOp.compC_of_mem (psiSigmaRaw_mem (Sc := Sc) (sy := sy) (hc := hc) μ i j)
    (lcross_mem (Sc := Sc) (sy := sy) (hc := hc) μ i j)]
  change _ • (_ • (_ • (cl D Sc μ [dn i, up j] [up j, dn i] (lcrossL i j) ≫
    cl D Sc μ [up j, dn i] [dn i, up j] (sigmaL i j)))) = 𝟙 _
  rw [smul_smul, smul_smul,
    show _ * _ * sign k (D.parity i * D.parity j * (D.parity i * D.parity j)) = 1 from
      (mul_comm _ _).trans (mixed_coeff t ht _ _), one_smul, cl_comp (sChain_lcrossL i j) (sChain_sigmaL i j),
    cl_invNe₂ Sc i j μ hij, cl_nil]
  rfl

private theorem wt_mixed_middle₁ (μ : X) (i j : I) :
    wt D μ [dn i, up i, up j, dn i] = wt D μ [up j, dn i] := by
  simp [wt, sh]

private theorem wt_mixed_middle₂ (μ : X) (i j : I) :
    wt D μ [dn i, up j, up i, dn i] = wt D μ [up j, dn i] := by
  simp [wt, sh]; abel

private theorem wt_up_pair (μ : X) (i j : I) :
    wt D μ [up i, up j] = wt D μ [up j, up i] := by
  simp [wt, sh]; abel

/-- First factor of the image of the defining mixed-crossing composite. -/
def psiSigmaCup (cs : CScalars Sc) (μ : X) (i j : I) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [up j, dn i]) μ [up j, dn i] rfl ⟶
      psiAt (wt D μ [up j, dn i]) μ [dn i, up i, up j, dn i] (wt_mixed_middle₁ μ i j) :=
  psiWhiskerRight _ μ [] [dn i, up i] [up j, dn i] rfl (by simp [wt, sh]) (psiCup cs _ i)

/-- Middle factor of the image of the defining mixed-crossing composite. -/
def psiSigmaMiddle (t : k) (μ : X) (i j : I) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [up j, dn i]) μ
      [dn i, up i, up j, dn i] (wt_mixed_middle₁ μ i j) ⟶
      psiAt (wt D μ [up j, dn i]) μ [dn i, up j, up i, dn i] (wt_mixed_middle₂ μ i j) :=
  psiWhiskerLeft _ (wt D μ [up i, up j, dn i]) μ [dn i] [up i, up j, dn i]
    [up j, up i, dn i] (wt_mixed_middle₁ μ i j)
    rfl (wt_up_pair (wt D μ [dn i]) j i)
    (psiWhiskerRight _ μ [up i, up j] [up j, up i] [dn i]
      rfl (wt_up_pair (wt D μ [dn i]) j i)
      (psiCross t _ (wt D μ [dn i]) i j rfl))

/-- Last factor of the image of the defining mixed-crossing composite. -/
def psiSigmaCap (cs : CScalars Sc) (μ : X) (i j : I) :
    psiAt (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [up j, dn i]) μ
      [dn i, up j, up i, dn i] (wt_mixed_middle₂ μ i j) ⟶
      psiAt (wt D μ [up j, dn i]) μ [dn i, up j] (wt_mixed μ i j) :=
  psiWhiskerLeft _ μ μ [dn i, up j] [up i, dn i] [] (wt_mixed μ i j)
    (by simp [wt, sh]) rfl (psiCap cs μ i)

private theorem ipar_dn (μ : X) (i j : I) : ipar D i (wt D μ [dn j]) = ipar D i μ := by
  have h := ipar_root (D := D) (wt D μ [dn j]) i j
  simpa [wt, sh] using h.symm

private theorem ipar_pair (μ : X) (i j : I) :
    ipar D i (wt D μ [up j, dn i]) = ipar D i μ :=
  (ipar_root (wt D μ [dn i]) i j).trans (ipar_dn μ i i)

private theorem psiSigmaCup_raw (cs : CScalars Sc) (μ : X) (i j : I) :
    SOp.unsop (psiSigmaCup (sy := sy) (hc := hc) cs μ i j) =
      capAt cs i μ [] [up j, dn i] := by
  unfold psiSigmaCup psiCup
  change SOp.unsop (psiWhiskerRight (sy := sy) (hc := hc) (wt D μ [up j, dn i]) μ
    [] [dn i, up i] [up j, dn i] rfl (by simp [wt, sh]) (SOp.mk' (epsP cs i _))) = _
  rw [psiWhiskerRight_mk (wt D μ [up j, dn i]) μ [] [dn i, up i] [up j, dn i]
    rfl (by simp [wt, sh]) (epsP_mem cs i _)]
  change _ = capAt cs i μ [] [up j, dn i]
  simp only [SOp.unsop_mk', psiParity, psiWordAt, ob, wd, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Bool.false_eq_true, ↓reduceIte]
  rw [ipar_pair]
  simp only [add_zero, zero_add, ipar_root, ipar_pair, zmod2_add_self, mul_zero, sign_zero, one_smul]
  rfl

private theorem psiSigmaCap_raw (cs : CScalars Sc) (μ : X) (i j : I) :
    SOp.unsop (psiSigmaCap (sy := sy) (hc := hc) cs μ i j) =
      cupAt cs i μ [dn i, up j] [] := by
  unfold psiSigmaCap psiCap
  rw [psiWhiskerLeft_mk _ _ _ _ _ _ _ _ _
    (Submodule.smul_mem _ _ (etaP_mem cs i μ))]
  change _ = cupAt cs i μ [dn i, up j] []
  simp only [SOp.unsop_mk', psiParity, psiWordAt, ob, wd, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Bool.false_eq_true, ↓reduceIte]
  rw [ipar_root]
  simp only [add_zero, zmod2_mul_self]
  change sign k (ipar D i μ) •
    ((plcL D Sc μ [dn i, up j] [] [] [up i, dn i])
      (sign k (ipar D i μ) • etaP cs i μ)) = cupAt cs i μ [dn i, up j] []
  exact (congrArg (fun f : (pres D Sc).obj (ob D μ [dn i, up j]) ⟶
      (pres D Sc).obj (ob D μ [dn i, up j, up i, dn i]) => sign k (ipar D i μ) • f)
    ((plcL D Sc μ [dn i, up j] [] [] [up i, dn i]).map_smul
      (sign k (ipar D i μ)) (etaP cs i μ))).trans (by
        rw [smul_smul, sign_mul_self, one_smul]; rfl)

private theorem psiSigmaMiddle_raw (t : k) (μ : X) (i j : I) :
    SOp.unsop (psiSigmaMiddle (Sc := Sc) (sy := sy) (hc := hc) t μ i j) =
      psiCoeff t (D.parity i * D.parity j) •
        cl D Sc μ [dn i, up j, up i, dn i] [dn i, up i, up j, dn i]
          (crossL [dn i] j i [dn i]) := by
  have hm : cl D Sc (wt D μ [dn i]) [up j, up i] [up i, up j] (crossL [] j i []) ∈
      homPar D Sc (wt D μ [dn i]) [up j, up i] [up i, up j] (D.parity i * D.parity j) :=
    cl_mem_homPar (by simp [crossL, Shape.dom, Shape.cod]) (by simp [parsum, mul_comm])
  unfold psiSigmaMiddle psiCross
  rw [psiWhiskerRight_mk _ _ _ _ _ _ _ (Submodule.smul_mem _ _ hm)]
  simp only [psiParity, psiWordAt, ob, wd, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Bool.false_eq_true, ↓reduceIte, add_zero, wt_nil]
  have hplace : plcL D Sc μ [] [dn i] [up j, up i] [up i, up j]
      (psiCoeff t (D.parity i * D.parity j) •
        cl D Sc (wt D μ [dn i]) [up j, up i] [up i, up j] (crossL [] j i [])) =
      psiCoeff t (D.parity i * D.parity j) •
        cl D Sc μ [up j, up i, dn i] [up i, up j, dn i] (crossL [] j i [dn i]) := by
    calc
      _ = psiCoeff t (D.parity i * D.parity j) •
          plcL D Sc μ [] [dn i] [up j, up i] [up i, up j]
            (cl D Sc (wt D μ [dn i]) [up j, up i] [up i, up j] (crossL [] j i [])) :=
        (plcL D Sc μ [] [dn i] [up j, up i] [up i, up j]).map_smul _ _
      _ = _ := by rw [plcL_cl]; rfl
  refine (congrArg (fun f : (pres D Sc).obj (ob D μ [up j, up i, dn i]) ⟶
      (pres D Sc).obj (ob D μ [up i, up j, dn i]) =>
    SOp.unsop (psiWhiskerLeft (sy := sy) (hc := hc) (wt D μ [up j, dn i])
      (wt D μ [up i, up j, dn i]) μ [dn i] [up i, up j, dn i] [up j, up i, dn i]
      (wt_mixed_middle₁ μ i j) rfl (wt_up_pair (wt D μ [dn i]) j i)
      (SOp.mk' (sign k (ipar D i μ * (D.parity i * D.parity j)) • f)))) hplace).trans ?_

  have hm' : cl D Sc μ [up j, up i, dn i] [up i, up j, dn i] (crossL [] j i [dn i]) ∈
      homPar D Sc μ [up j, up i, dn i] [up i, up j, dn i] (D.parity i * D.parity j) :=
    cl_mem_homPar (by simp [crossL, Shape.dom, Shape.cod]) (by simp [parsum, mul_comm])
  rw [psiWhiskerLeft_mk _ _ _ _ _ _ _ _ _
    (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hm'))]
  simp only [SOp.unsop_mk', psiParity, psiWordAt, ob, wd, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Bool.false_eq_true, ↓reduceIte, add_zero]
  change sign k (ipar D i (wt D μ [up i, up j, dn i]) * (D.parity i * D.parity j)) •
    plcL D Sc μ [dn i] [] [up j, up i, dn i] [up i, up j, dn i]
      (sign k (ipar D i μ * (D.parity i * D.parity j)) •
        (psiCoeff t (D.parity i * D.parity j) •
          cl D Sc μ [up j, up i, dn i] [up i, up j, dn i] (crossL [] j i [dn i]))) = _
  rw [show ipar D i (wt D μ [up i, up j, dn i]) = ipar D i μ from
    (ipar_root (wt D μ [up j, dn i]) i i).trans (ipar_pair μ i j),
    (plcL D Sc μ [dn i] [] [up j, up i, dn i] [up i, up j, dn i]).map_smul,
    (plcL D Sc μ [dn i] [] [up j, up i, dn i] [up i, up j, dn i]).map_smul,
    smul_smul, sign_mul_self, one_smul]
  exact congrArg (fun f : (pres D Sc).obj (ob D μ [dn i, up j, up i, dn i]) ⟶
      (pres D Sc).obj (ob D μ [dn i, up i, up j, dn i]) =>
        psiCoeff t (D.parity i * D.parity j) • f)
    (plcL_cl D Sc μ [dn i] [] [up j, up i, dn i] [up i, up j, dn i] (crossL [] j i [dn i]))

/-- The image of (1.11), calculated from the assigned cup, crossing, and cap
using the actual target whiskerings. -/
theorem psiSigma_eq_composite (cs : CScalars Sc) (t : k) (μ : X) (i j : I) :
    psiSigmaCup (sy := sy) (hc := hc) cs μ i j ≫ psiSigmaMiddle t μ i j ≫
      psiSigmaCap cs μ i j = psiSigma t μ i j := by
  have hcup : psiSigmaCup (sy := sy) (hc := hc) cs μ i j ∈ parity (R := k) _ _ 0 :=
    psiWhiskerRight_mem (sy := sy) (hc := hc) (wt D μ [up j, dn i]) μ
      [] [dn i, up i] [up j, dn i] rfl (by simp [wt, sh])
      (psiCup_mem_parity cs (wt D μ [up j, dn i]) i)
  have hcap : psiSigmaCap (sy := sy) (hc := hc) cs μ i j ∈ parity (R := k) _ _ 0 :=
    psiWhiskerLeft_mem (sy := sy) (hc := hc) (wt D μ [up j, dn i]) μ μ
      [dn i, up j] [up i, dn i] [] (wt_mixed μ i j) (by simp [wt, sh]) rfl
      (psiCap_mem_parity cs μ i)
  have hmid : psiSigmaMiddle (Sc := Sc) (sy := sy) (hc := hc) t μ i j ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
    psiWhiskerLeft_mem (sy := sy) (hc := hc) (wt D μ [up j, dn i])
      (wt D μ [up i, up j, dn i]) μ [dn i] [up i, up j, dn i] [up j, up i, dn i]
      (wt_mixed_middle₁ μ i j) rfl (wt_up_pair (wt D μ [dn i]) j i)
      (psiWhiskerRight_mem (wt D μ [up i, up j, dn i]) μ [up i, up j] [up j, up i] [dn i]
        rfl (wt_up_pair (wt D μ [dn i]) j i)
        (psiCross_mem_parity t (wt D μ [up i, up j, dn i]) (wt D μ [dn i]) i j rfl))
  have hmc : psiSigmaMiddle (Sc := Sc) (sy := sy) (hc := hc) t μ i j ≫
      psiSigmaCap cs μ i j ∈ parity (R := k) _ _ (D.parity i * D.parity j) := by
    simpa only [add_zero] using comp_mem hmid hcap
  apply SOp.hom_ext
  rw [SOp.comp_of_mem (f := psiSigmaCup (sy := sy) (hc := hc) cs μ i j)
    (g := psiSigmaMiddle t μ i j ≫ psiSigmaCap cs μ i j) hcup hmc,
    SOp.comp_of_mem (f := psiSigmaMiddle (sy := sy) (hc := hc) t μ i j)
      (g := psiSigmaCap cs μ i j) hmid hcap]
  simp only [zero_mul, mul_zero, sign_zero, one_smul]
  rw [psiSigmaCup_raw, psiSigmaCap_raw, psiSigmaMiddle_raw]
  change (cupAt cs i μ [dn i, up j] [] ≫
      (psiCoeff t (D.parity i * D.parity j) •
        cl D Sc μ [dn i, up j, up i, dn i] [dn i, up i, up j, dn i]
          (crossL [dn i] j i [dn i]))) ≫ capAt cs i μ [] [up j, dn i] =
    (psiCoeff t (D.parity i * D.parity j) * sign k (D.parity i * D.parity j * ipar D i μ)) •
      cl D Sc μ [dn i, up j] [up j, dn i] (lcrossL i j)
  rw [Linear.comp_smul, Linear.smul_comp, Category.assoc,
    rot_tau_left cs j i μ, ← sign_eq_zsign, smul_smul]

/-- The mixed-crossing image has the source parity. -/
theorem psiSigma_mem_parity (t : k) (μ : X) (i j : I) :
    psiSigma (Sc := Sc) (sy := sy) (hc := hc) t μ i j ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  Submodule.smul_mem _ _ (lcross_mem μ i j)

/-- The inverse-crossing image has the source parity. -/
theorem psiLCross_mem_parity (t : k) (μ : X) (i j : I) :
    psiLCross (Sc := Sc) (sy := sy) (hc := hc) t μ i j ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  Submodule.smul_mem _ _ (psiSigmaRaw_mem μ i j)

/-- The mixed-crossing image has integer degree zero. -/
theorem psiSigma_mem_degree (t : k) (μ : X) (i j : I) :
    psiSigma (Sc := Sc) (sy := sy) (hc := hc) t μ i j ∈
      GradedSupercategory.degree (R := k) _ _ 0 := by
  change (_ : k) • cl D Sc μ [dn i, up j] [up j, dn i] (lcrossL i j) ∈
    (pres D Sc).homDeg (gdeg D sy) _ _ (0 + (0 - 0))
  apply Submodule.smul_mem
  rw [cl_of (sChain_lcrossL i j)]
  apply Presentation.diag_mem_homDeg'
  simpa only [sub_self, add_zero] using
    (degree_gdeg_mkD D sy μ (lcrossL i j) (sChain_lcrossL i j)).trans (gsum_lcrossL D sy μ i j)

/-- The inverse-crossing image has integer degree zero. -/
theorem psiLCross_mem_degree (t : k) (μ : X) (i j : I) :
    psiLCross (Sc := Sc) (sy := sy) (hc := hc) t μ i j ∈
      GradedSupercategory.degree (R := k) _ _ 0 := by
  change (_ : k) • cl D Sc μ [up j, dn i] [dn i, up j] (sigmaL i j) ∈
    (pres D Sc).homDeg (gdeg D sy) _ _ (0 + (0 - 0))
  apply Submodule.smul_mem
  rw [cl_of (sChain_sigmaL i j)]
  apply Presentation.diag_mem_homDeg'
  simpa only [sub_self, add_zero] using
    (degree_gdeg_mkD D sy μ (sigmaL i j) (sChain_sigmaL i j)).trans (gsum_sigmaL D sy μ i j)

/-- The distinct-colour inversion requirement (1.12), for the actual whiskered
images of the printed assignments in Proposition 9.4. -/
theorem psiMixed_inversion (cs : CScalars Sc) (t : k) (ht : t ^ 2 = -1)
    (μ : X) (i j : I) (hij : i ≠ j) :
    ((psiSigmaCup (sy := sy) (hc := hc) cs μ i j ≫ psiSigmaMiddle t μ i j ≫
        psiSigmaCap cs μ i j) ≫ psiLCross t μ i j = 𝟙 _) ∧
      (psiLCross (sy := sy) (hc := hc) t μ i j ≫ (psiSigmaCup cs μ i j ≫ psiSigmaMiddle t μ i j ≫
        psiSigmaCap cs μ i j) = 𝟙 _) := by
  rw [psiSigma_eq_composite]
  exact ⟨psi_invNe₁ t ht μ i j hij, psi_invNe₂ t ht μ i j hij⟩

end OddMath.SKM
