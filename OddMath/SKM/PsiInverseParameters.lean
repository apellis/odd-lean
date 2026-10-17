/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PitchforkCap
import OddMath.SKM.PsiLeftImages
import OddMath.SKM.PsiQuotient
import OddMath.SKM.PsiInverse

/-!
# Inverse parameters and cup/cap roundtrips for ψ

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 9.4 asserts an isomorphism and constructs the forward map. The
parameter change proved here is a derived formula, not an inverse formula
printed in the proposition:
`(t, c_{μ;i}) ↦ (-t, psiCoeff t (ipar D i μ) * c_{μ;i})`.

The rescaled coefficients are units satisfying the same root-shift law, and
changing parameters twice recovers the original coefficients. Both orders
of the cup and cap roundtrips are proved using `psiMap₂` on the presentation
quotient. The intervening Π shifts are conjugated by `psiPiConjugate`; its
proved boundary-transport formula justifies the final heterogeneous equality.
In the cup calculation this conjugation contributes `sign k (ipar D i μ)`;
in the cap calculation its sign is one. Omitting it is not the same formula.

These statements hold at every weight, including zero, over an ordinary
commutative ring with a specified square root of `-1`. This is the purely
even specialization of the source's supercommutative ground ring; no field
hypothesis is used (the source singles out purely even fields as its main
case of interest). No nonvanishing assumption on any cup or cap is made.

This supplies generator-level inverse calculations for Proposition 9.4.
It does not construct an inverse on all envelope morphisms or establish
its composition and identity comparisons.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-- The ψ coefficient as a unit, with inverse obtained from `-t`. -/
def psiCoeffUnit (t : k) (ht : t ^ 2 = -1) (p : ZMod 2) : kˣ where
  val := psiCoeff t p
  inv := psiCoeff (-t) p
  val_inv := by rw [mul_comm]; exact psiCoeff_neg_mul ht p
  inv_val := psiCoeff_neg_mul ht p

@[simp] theorem psiCoeffUnit_val (t : k) (ht : t ^ 2 = -1) (p : ZMod 2) :
    (psiCoeffUnit t ht p : k) = psiCoeff t p := rfl
@[simp] theorem psiCoeffUnit_inv_val (t : k) (ht : t ^ 2 = -1) (p : ZMod 2) :
    ((psiCoeffUnit t ht p)⁻¹ : kˣ) = psiCoeffUnit (-t) (psi_neg_sq ht) p := by
  apply Units.ext; rfl

/-- Rescale the auxiliary units without changing `D` or `Sc`. -/
def psiInverseCScalars (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) : CScalars Sc where
  c μ i := psiCoeffUnit t ht (ipar D i μ) * cs.c μ i
  shift μ i j := by
    have hp : ipar D i (μ + D.α j) = ipar D i μ := by
      simpa [wt, sh, add_comm] using ipar_wt_upj (D := D) i j μ
    rw [hp, cs.shift]
    ac_rfl

/-- The rescaling is undone by the opposite square root. -/
@[simp] theorem psiInverseCScalars_involutive (t : k) (ht : t ^ 2 = -1)
    (cs : CScalars Sc) :
    psiInverseCScalars (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs) = cs := by
  cases cs with
  | mk c shift =>
    unfold psiInverseCScalars
    congr 1
    funext μ i
    apply Units.ext
    change psiCoeff (-t) (ipar D i μ) * (psiCoeff t (ipar D i μ) * _) = _
    rw [← mul_assoc, psiCoeff_neg_mul ht, one_mul]

/-- The derived left cup scales by the new auxiliary unit. -/
theorem etaP_psiInverseCScalars (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) :
    etaP (psiInverseCScalars t ht cs) i μ = psiCoeff t (ipar D i μ) • etaP cs i μ := by
  unfold etaP
  split_ifs <;> simp only [psiInverseCScalars, Units.val_mul, psiCoeffUnit, smul_smul]
  congr 1; ring

/-- The derived left cap scales by the inverse auxiliary unit. -/
theorem epsP_psiInverseCScalars (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)
    (μ : X) (i : I) :
    epsP (psiInverseCScalars t ht cs) i μ = psiCoeff (-t) (ipar D i μ) • epsP cs i μ := by
  unfold epsP
  split_ifs <;> simp only [psiInverseCScalars, mul_inv_rev, Units.val_mul,
    psiCoeffUnit_inv_val, psiCoeffUnit_val, smul_smul]
  · congr 1; exact mul_comm _ _
  · congr 1; ring

private theorem wt_du (μ : X) (i : I) : wt D μ [dn i, up i] = μ := by
  simp [wt_cons, sh, dn, up]
private theorem wt_ud (μ : X) (i : I) : wt D μ [up i, dn i] = μ := by
  simp [wt_cons, sh, dn, up]

/-- The quotient map on the derived left cup, at every weight. -/
theorem psiMap₂_etaP (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (μ : X) (i : I) :
    psiMap₂ (sy := sy) (hc := hc) t ht cs
      (psiWordAt μ μ [] rfl) (psiWordAt μ μ [up i, dn i] (wt_ud μ i)) (etaP cs i μ) =
      psiLeftCupImage t μ i := by
  rw [← etaPDiagram_lin, psiMap₂_lin]
  exact psiLin_etaP cs t ht μ i

/-- The quotient map on the derived left cap, at every weight. -/
theorem psiMap₂_epsP (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (μ : X) (i : I) :
    psiMap₂ (sy := sy) (hc := hc) t ht cs
      (psiWordAt μ μ [dn i, up i] (wt_du μ i)) (psiWordAt μ μ [] rfl) (epsP cs i μ) =
      psiLeftCapImage t μ i := by
  rw [← epsPDiagram_lin, psiMap₂_lin]
  exact psiLin_epsP cs t ht μ i

/-- The quotient map recovers the prescribed right-cup assignment. -/
theorem psiMap₂_cup (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (μ : X) (i : I) :
    psiMap₂ (sy := sy) (hc := hc) t ht cs
      (psiWordAt μ μ [] rfl) (psiWordAt μ μ [dn i, up i] (wt_du μ i))
      (cl D Sc μ [] [dn i, up i] (etaL i 0)) = psiCup cs μ i := by
  rw [cl_of (sChain_etaL i 0), psiMap₂_diag, psiDiagram_mkD]
  change psiRaw t cs μ μ [⟨[], .cup i, []⟩] rfl (wt_du μ i) _ = _
  rw [psiRaw_gen]
  rfl

/-- The quotient map recovers the prescribed right-cap assignment. -/
theorem psiMap₂_cap (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) (μ : X) (i : I) :
    psiMap₂ (sy := sy) (hc := hc) t ht cs
      (psiWordAt μ μ [up i, dn i] (wt_ud μ i)) (psiWordAt μ μ [] rfl)
      (cl D Sc μ [up i, dn i] [] (epsL i 0)) = psiCap cs μ i := by
  rw [cl_of (sChain_epsL i 0), psiMap₂_diag, psiDiagram_mkD]
  change psiRaw t cs μ μ [⟨[], .cap i, []⟩] (wt_ud μ i) rfl _ = _
  rw [psiRaw_gen]
  rfl

private theorem homPar_mem {μ : X} {s r : List (Letter I)} {p : ZMod 2}
    {x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ r)}
    (hx : x ∈ homPar D Sc μ s r p) :
    x ∈ (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ p := by
  refine Submodule.span_le.mpr ?_ hx
  rintro x ⟨L, hL, hp, rfl⟩
  rw [cl_of hL]
  apply Presentation.diag_mem_homDeg'
  rw [degree_parity_mkD]
  exact hp

/-- First `(t, cs)`, then the inverse parameters: the cup returns after Π conjugation.
The input to the second quotient map is the original `epsP cs`, not the rescaled cap. -/
theorem psiCup_parameter_roundtrip (t : k) (ht : t ^ 2 = -1)
    (cs : CScalars Sc) (μ : X) (i : I) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop
      (psiPiConjugate (ipar D i μ) 0
        (psiMap₂ (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
          (psiWordAt μ μ [dn i, up i] (wt_du μ i)) (psiWordAt μ μ [] rfl)
          (QPiTwoEnvelope.toHom (SOp.unsop (psiMap₂ (sy := sy) (hc := hc) t ht cs
            (psiWordAt μ μ [] rfl) (psiWordAt μ μ [dn i, up i] (wt_du μ i))
            (cl D Sc μ [] [dn i, up i] (etaL i 0)))))))))
      (cl D Sc μ [] [dn i, up i] (etaL i 0)) := by
  rw [psiMap₂_cup]
  change HEq (QPiTwoEnvelope.toHom (SOp.unsop
    (psiPiConjugate (ipar D i μ) 0
      (psiMap₂ (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
        (psiWordAt μ μ [dn i, up i] (wt_du μ i)) (psiWordAt μ μ [] rfl)
        (epsP cs i μ))))) _
  have hh := psiPiConjugate_heq (ipar D i μ) 0 (ipar D i μ)
    (psiMap₂_mem_parity (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
      (f := psiWordAt (Sc := Sc) μ μ [dn i, up i] (wt_du μ i))
      (g := psiWordAt μ μ [] rfl) (sy := sy) (hc := hc)
      (homPar_mem (epsP_mem cs i μ)))
  refine hh.trans (heq_of_eq ?_)
  have he : epsP cs i μ = psiCoeff t (ipar D i μ) •
      epsP (psiInverseCScalars t ht cs) i μ := by
    simpa using epsP_psiInverseCScalars (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs) μ i
  rw [he, map_smul, psiMap₂_epsP]
  change sign k (ipar D i μ * ipar D i μ + (ipar D i μ + ipar D i μ) * 0 + 0) •
    (psiCoeff t (ipar D i μ) • ((psiCoeff (-t) (ipar D i μ) * sign k (ipar D i μ)) • _)) = _
  have hp : ipar D i μ * ipar D i μ = ipar D i μ := by
    rcases parity_eq_zero_or_one (ipar D i μ) with h | h <;> simp [h]
  simp only [mul_zero, add_zero, hp, smul_smul]
  rw [← mul_assoc (psiCoeff t _), mul_comm (psiCoeff t _), psiCoeff_neg_mul ht,
    one_mul, sign_mul_self, one_smul]

/-- First `(t, cs)`, then the inverse parameters: the cap returns after Π conjugation.
The input to the second quotient map retains the sign on the original `etaP cs`. -/
theorem psiCap_parameter_roundtrip (t : k) (ht : t ^ 2 = -1)
    (cs : CScalars Sc) (μ : X) (i : I) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop
      (psiPiConjugate 0 (ipar D i μ)
        (psiMap₂ (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
          (psiWordAt μ μ [] rfl) (psiWordAt μ μ [up i, dn i] (wt_ud μ i))
          (QPiTwoEnvelope.toHom (SOp.unsop (psiMap₂ (sy := sy) (hc := hc) t ht cs
            (psiWordAt μ μ [up i, dn i] (wt_ud μ i)) (psiWordAt μ μ [] rfl)
            (cl D Sc μ [up i, dn i] [] (epsL i 0)))))))))
      (cl D Sc μ [up i, dn i] [] (epsL i 0)) := by
  rw [psiMap₂_cap]
  change HEq (QPiTwoEnvelope.toHom (SOp.unsop
    (psiPiConjugate 0 (ipar D i μ)
      (psiMap₂ (sy := sy) (hc := hc) (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
        (psiWordAt μ μ [] rfl) (psiWordAt μ μ [up i, dn i] (wt_ud μ i))
        (sign k (ipar D i μ) • etaP cs i μ))))) _
  have hh := psiPiConjugate_heq 0 (ipar D i μ) (ipar D i μ)
    (psiMap₂_mem_parity (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
      (f := psiWordAt (Sc := Sc) μ μ [] rfl)
      (g := psiWordAt μ μ [up i, dn i] (wt_ud μ i)) (sy := sy) (hc := hc)
      (Submodule.smul_mem _ (sign k (ipar D i μ)) (homPar_mem (etaP_mem cs i μ))))
  refine hh.trans (heq_of_eq ?_)
  have he : etaP cs i μ = psiCoeff (-t) (ipar D i μ) •
      etaP (psiInverseCScalars t ht cs) i μ := by
    simpa using etaP_psiInverseCScalars (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs) μ i
  rw [he, map_smul, map_smul, psiMap₂_etaP]
  change sign k (0 * ipar D i μ + (0 + ipar D i μ) * ipar D i μ + ipar D i μ) •
    (sign k (ipar D i μ) • (psiCoeff (-t) (ipar D i μ) •
      (psiCoeff (-t) (ipar D i μ) • _))) = _
  have hp : ipar D i μ * ipar D i μ + ipar D i μ = 0 := by
    rcases parity_eq_zero_or_one (ipar D i μ) with h | h <;> simp [h, show (1 : ZMod 2) + 1 = 0 from rfl]
  simp only [zero_mul, zero_add, hp, sign_zero, smul_smul]
  rw [one_mul, psiCoeff_mul_self (psi_neg_sq ht), sign_mul_self, one_smul]

/-- First the inverse parameters, then `(t, cs)`: the cup roundtrip. -/
theorem psiCup_parameter_roundtrip_reverse (t : k) (ht : t ^ 2 = -1)
    (cs : CScalars Sc) (μ : X) (i : I) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop
      (psiPiConjugate (ipar D i μ) 0
        (psiMap₂ (sy := sy) (hc := hc) t ht cs
          (psiWordAt μ μ [dn i, up i] (wt_du μ i)) (psiWordAt μ μ [] rfl)
          (QPiTwoEnvelope.toHom (SOp.unsop (psiMap₂ (sy := sy) (hc := hc)
            (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
            (psiWordAt μ μ [] rfl) (psiWordAt μ μ [dn i, up i] (wt_du μ i))
            (cl D Sc μ [] [dn i, up i] (etaL i 0)))))))))
      (cl D Sc μ [] [dn i, up i] (etaL i 0)) := by
  simpa only [neg_neg, psiInverseCScalars_involutive] using
    psiCup_parameter_roundtrip (sy := sy) (hc := hc) (-t) (psi_neg_sq ht)
      (psiInverseCScalars t ht cs) μ i

/-- First the inverse parameters, then `(t, cs)`: the cap roundtrip. -/
theorem psiCap_parameter_roundtrip_reverse (t : k) (ht : t ^ 2 = -1)
    (cs : CScalars Sc) (μ : X) (i : I) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop
      (psiPiConjugate 0 (ipar D i μ)
        (psiMap₂ (sy := sy) (hc := hc) t ht cs
          (psiWordAt μ μ [] rfl) (psiWordAt μ μ [up i, dn i] (wt_ud μ i))
          (QPiTwoEnvelope.toHom (SOp.unsop (psiMap₂ (sy := sy) (hc := hc)
            (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
            (psiWordAt μ μ [up i, dn i] (wt_ud μ i)) (psiWordAt μ μ [] rfl)
            (cl D Sc μ [up i, dn i] [] (epsL i 0)))))))))
      (cl D Sc μ [up i, dn i] [] (epsL i 0)) := by
  simpa only [neg_neg, psiInverseCScalars_involutive] using
    psiCap_parameter_roundtrip (sy := sy) (hc := hc) (-t) (psi_neg_sq ht)
      (psiInverseCScalars t ht cs) μ i

end OddMath.SKM
