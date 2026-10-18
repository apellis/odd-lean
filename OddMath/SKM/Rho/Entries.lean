import OddMath.SKM.Rho.Normalized
import OddMath.SKM.Rho.DottedMatrixEntries

/-!
# Entries for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoInversionKernel
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords RhoEvaluator RhoMixed
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem wt_ud (μ : X) (i : I) : wt D μ [up i, dn i] = μ := by simp [wt, sh]
theorem wt_du (μ : X) (i : I) : wt D μ [dn i, up i] = μ := by simp [wt, sh]

theorem norm_sigma (t : k) (ν μ : X) (i j : I)
    (hs : wt D μ [up j, dn i] = ν) (hr : wt D μ [dn i, up j] = ν) :
    normLin (Sc := Sc) (sy := sy) (hc := hc) t ν μ hs hr
      (dg D μ (sigmaL i j) (sChain_sigmaL i j)) = mixed t ν i j := by
  rw [norm_dg]
  change (1 * (psiCoeff t (D.parity i * D.parity j) * (1 * 1))) •
    cl D Sc ν [up i, dn j] [dn j, up i] _ = _
  simp only [one_mul, mul_one]
  congr 1

theorem norm_lcross (t : k) (ν μ : X) (i j : I)
    (hs : wt D μ [dn i, up j] = ν) (hr : wt D μ [up j, dn i] = ν) :
    normLin (Sc := Sc) (sy := sy) (hc := hc) t ν μ hs hr
      (dg D μ (lcrossL i j) (sChain_lcrossL i j)) = mixedInverse t ν i j := by
  rw [norm_dg]
  change (psiCoeff (-t) (D.parity i * D.parity j) * 1) •
    cl D Sc ν [dn j, up i] [up i, dn j] _ = _
  simp only [mul_one]
  rfl

theorem imageCoeff_dots (t : k) (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℕ) :
    imageCoeff (D := D) t (dotsL u i v n) = psiCoeff t (D.parity i) ^ n := by
  induction n with
  | zero => exact (pow_zero _).symm
  | succ n ih =>
    change psiCoeff t (D.parity i) * imageCoeff (D := D) t (dotsL u i v n) = _
    rw [ih, pow_succ']

theorem imageLayers_dots (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℕ) :
    imageLayers (dotsL u i v n) = (ddotsL i n).map (whL (rhoWord v) (rhoWord u)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (ddotL i).map (whL (rhoWord v) (rhoWord u)) ++ imageLayers (dotsL u i v n) = _
    rw [ih]
    simp only [ddotsL, List.replicate_succ, List.flatten_cons, List.map_append]

theorem norm_eps (t : k) (μ : X) (i : I) (n : ℕ) :
    normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ (wt_ud μ i) rfl
      (dg D μ (epsL i n) (sChain_epsL i n)) = epsImage t μ i n := by
  rw [norm_dg]
  simp only [epsL, imageCoeff_append, imageCoeff_dots, imageCoeff, RhoGenerators.coeff,
    mul_one, imageLayers_append, imageLayers_dots]
  rfl

theorem norm_eta (t : k) (μ : X) (i : I) (n : ℕ) :
    normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ rfl (wt_du μ i)
      (dg D μ (etaL i n) (sChain_etaL i n)) = etaImage t μ i n := by
  rw [norm_dg]
  simp only [etaL, imageCoeff_append, imageCoeff_dots, imageCoeff, RhoGenerators.coeff,
    one_mul, imageLayers_append, imageLayers_dots]
  rfl

theorem norm_dcup (t : k) (μ : X) (i : I) (n : ℕ) :
    normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ rfl (wt_ud μ i)
      (dg D μ (dcupL i n) (sChain_dcupL i n)) = cupDiamond t μ i n := by
  rw [norm_dg]
  change (entryCoeff (-t) (D.parity i) n * 1) • cl D Sc μ [] [up i, dn i] _ = _
  rw [mul_one]
  rfl

theorem norm_dcap (t : k) (μ : X) (i : I) (n : ℕ) :
    normLin (Sc := Sc) (sy := sy) (hc := hc) t μ μ (wt_du μ i) rfl
      (dg D μ (dcapL i n) (sChain_dcapL i n)) = capDiamond t μ i n := by
  rw [norm_dg]
  change (entryCoeff (-t) (D.parity i) n * 1) • cl D Sc μ [dn i, up i] [] _ = _
  rw [mul_one]
  rfl

end OddMath.SKM.RhoInversionKernel
