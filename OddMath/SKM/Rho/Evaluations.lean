import OddMath.SKM.Rho.Reflected

/-!
# Evaluations for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoMates
open CategoryTheory StringDiagrams Presentation RhoWords RhoEvaluator RhoInversionKernel RhoTwo RhoExtension
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem quotient_ddot (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I)
    (h : wt D μ [dn i] = ν) :
    HEq (rhoQuotient (sy := sy) (hc := hc) t ht ν μ h h
      (cl D Sc μ [dn i] [dn i] (ddotL i)))
      (psiCoeff t (D.parity i) • cl D Sc ν [up i] [up i] (dotsL [] i [] 1)) := by
  rw [cl_of (sChain_ddotL i), rhoQuotient_diag, rhoDiagram_mkD]
  have H := raw_formula (Sc := Sc) (sy := sy) (hc := hc) t ν μ (ddotL i) h h (sChain_ddotL i)
  change HEq _ (imageCoeff (D := D) t (ddotL i) •
    cl D Sc ν [up i] [up i] (imageLayers (ddotL i))) at H
  rw [ddot_coeff, reflected_ddot] at H
  exact H

theorem quotient_dcross (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (hs : wt D μ [dn j, dn i] = ν) (hr : wt D μ [dn i, dn j] = ν) :
    HEq (rhoQuotient (sy := sy) (hc := hc) t ht ν μ hs hr
      (cl D Sc μ [dn j, dn i] [dn i, dn j] (dcrossL j i)))
      (psiCoeff t (D.parity i * D.parity j) •
        cl D Sc ν [up i, up j] [up j, up i] (crossL [] i j [])) := by
  have ch : SChain [dn j, dn i] (dcrossL j i) [dn i, dn j] := by
    rw [dcrossL_eq_mateN]
    exact sChain_mateN (show SChain (ups [j,i]) (crossL [] j i []) (ups [i,j]) from ⟨rfl,rfl⟩)
  rw [cl_of ch, rhoQuotient_diag, rhoDiagram_mkD]
  have H := raw_formula (Sc := Sc) (sy := sy) (hc := hc) t ν μ (dcrossL j i) hs hr ch
  change HEq _ (imageCoeff (D := D) t (dcrossL j i) •
    cl D Sc ν [up i, up j] [up j, up i] (imageLayers (dcrossL j i))) at H
  rw [dcross_coeff, reflected_dcross] at H
  exact H

end OddMath.SKM.RhoMates
