import OddMath.SKM.Rho.Contractions

/-!
# Reflected for ρ

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

theorem reflected_ddot (μ : X) (i : I) :
    cl D Sc μ [up i] [up i] (imageLayers (ddotL i)) =
      cl D Sc μ [up i] [up i] (dotsL [] i [] 1) := by
  have H := unmate_mate (Sc := Sc) μ (sChain_cupN [i]) (sChain_capN [i])
    (sChain_capN [i]) (sChain_dotsL [] i [] 1) (parsum_cupN (D := D) [i])
    (parsum_capN (D := D) [i]) (zigE_N Sc [i]) (zigE_N Sc [i])
  simpa [imageLayers, ddotL, mateL, mateB, cupN, capN, dotsL,
    RhoGenerators.layers, rhoWord, flipW, flipL, whL, ups, dns] using H

theorem reflected_dcross (μ : X) (i j : I) :
    cl D Sc μ [up i, up j] [up j, up i] (imageLayers (dcrossL j i)) =
      cl D Sc μ [up i, up j] [up j, up i] (crossL [] i j []) := by
  have H := unmate_mate (Sc := Sc) μ (sChain_cupN [j,i]) (sChain_capN [i,j])
    (sChain_capN [j,i]) (show SChain (ups [i,j]) (crossL [] i j []) (ups [j,i]) from ⟨rfl, rfl⟩) (parsum_cupN (D := D) [j,i])
    (parsum_capN (D := D) [i,j]) (zigE_N Sc [i,j]) (zigE_N Sc [j,i])
  simpa [imageLayers, dcrossL, sigmaL, mateB, cupN, capN, crossL,
    RhoGenerators.layers, rhoWord, flipW, flipL, whL, ups, dns] using H

theorem ddot_coeff (t : k) (i : I) :
    imageCoeff (D := D) t (ddotL i) = psiCoeff t (D.parity i) := by
  simp [imageCoeff, ddotL, mateL, dotsL, whL, RhoGenerators.coeff]

theorem dcross_coeff (t : k) (i j : I) :
    imageCoeff (D := D) t (dcrossL j i) = psiCoeff t (D.parity i * D.parity j) := by
  simp [imageCoeff, dcrossL, sigmaL, whL, RhoGenerators.coeff, mul_comm]

end OddMath.SKM.RhoMates
