import OddMath.SKM.Rho.Mixed

/-!
# Matrix for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoMixed
open CategoryTheory StringDiagrams Supercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

def entryCoeff (t : k) (p : ZMod 2) (n : ℕ) : k :=
  psiCoeff t p ^ n * zsign k (p * ((n / 2 : ℕ) : ZMod 2))

theorem entryCoeff_inverse (t : k) (ht : t ^ 2 = -1) (p : ZMod 2) (n : ℕ) :
    entryCoeff t p n * entryCoeff (-t) p n = 1 := by
  unfold entryCoeff
  calc
    _ = (psiCoeff t p * psiCoeff (-t) p) ^ n *
        (zsign k (p * ((n / 2 : ℕ) : ZMod 2)) * zsign k (p * ((n / 2 : ℕ) : ZMod 2))) := by ring
    _ = 1 := by rw [coeff_inverse t ht, one_pow, zsign_mul_self, mul_one]

def epsImage (t : k) (ν : X) (i : I) (n : ℕ) :=
  psiCoeff t (D.parity i) ^ n • cl D Sc ν [up i, dn i] []
    ((ddotsL i n).map (whL [up i] []) ++ [([], Shape.cap i, [])])

def etaImage (t : k) (ν : X) (i : I) (n : ℕ) :=
  psiCoeff t (D.parity i) ^ n • cl D Sc ν [] [dn i, up i]
    ([([], Shape.cup i, [])] ++ (ddotsL i n).map (whL [] [up i]))

theorem epsImage_eq (t : k) (ν : X) (i : I) (n : ℕ) :
    epsImage (Sc := Sc) t ν i n = entryCoeff t (D.parity i) n •
      cl D Sc ν [up i, dn i] [] (epsL i n) := by
  have H := congrArg (zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) • ·)
    (eq_2_3_b Sc i ν n)
  simp only [smul_smul, zsign_mul_self, one_smul] at H
  rw [epsImage, ← H, smul_smul]
  congr 1
  simp [epsL, dotsL, whL]

theorem etaImage_eq (t : k) (ν : X) (i : I) (n : ℕ) :
    etaImage (Sc := Sc) t ν i n = entryCoeff t (D.parity i) n •
      cl D Sc ν [] [dn i, up i] (etaL i n) := by
  have H := congrArg (zsign k (D.parity i * ((n / 2 : ℕ) : ZMod 2)) • ·)
    (eq_2_3_a Sc i ν n)
  simp only [smul_smul, zsign_mul_self, one_smul] at H
  rw [etaImage, ← H, smul_smul]
  congr 1
  simp [etaL, dotsL, whL]

def cupDiamond (t : k) (ν : X) (i : I) (n : ℕ) :=
  entryCoeff (-t) (D.parity i) n • cl D Sc ν [] [up i, dn i] (dcupL i n)

def capDiamond (t : k) (ν : X) (i : I) (n : ℕ) :=
  entryCoeff (-t) (D.parity i) n • cl D Sc ν [dn i, up i] [] (dcapL i n)

theorem mixed_same_comp (t : k) (ht : t ^ 2 = -1) (ν : X) (i : I) :
    mixed (Sc := Sc) t ν i i ≫ mixedInverse t ν i i =
      cl D Sc ν [up i, dn i] [up i, dn i] (sigmaL i i ++ lcrossL i i) := by
  rw [mixed_eq, mixedInverse, Linear.smul_comp, Linear.comp_smul, smul_smul,
    coeff_inverse t ht, one_smul, cl_comp (sChain_sigmaL i i) (sChain_lcrossL i i)]

theorem mixed_same_comp' (t : k) (ht : t ^ 2 = -1) (ν : X) (i : I) :
    mixedInverse (Sc := Sc) t ν i i ≫ mixed t ν i i =
      cl D Sc ν [dn i, up i] [dn i, up i] (lcrossL i i ++ sigmaL i i) := by
  rw [mixed_eq, mixedInverse, Linear.smul_comp, Linear.comp_smul, smul_smul,
    mul_comm (psiCoeff (-t) _), coeff_inverse t ht, one_smul,
    cl_comp (sChain_lcrossL i i) (sChain_sigmaL i i)]

theorem eps_cupDiamond (t : k) (ht : t ^ 2 = -1) (ν : X) (i : I) (n : ℕ) :
    epsImage (Sc := Sc) t ν i n ≫ cupDiamond t ν i n =
      cl D Sc ν [up i, dn i] [up i, dn i] (epsL i n ++ dcupL i n) := by
  rw [epsImage_eq, cupDiamond, Linear.smul_comp, Linear.comp_smul, smul_smul,
    entryCoeff_inverse t ht, one_smul, cl_comp (sChain_epsL i n) (sChain_dcupL i n)]

theorem capDiamond_eta (t : k) (ht : t ^ 2 = -1) (ν : X) (i : I) (n : ℕ) :
    capDiamond (Sc := Sc) t ν i n ≫ etaImage t ν i n =
      cl D Sc ν [dn i, up i] [dn i, up i] (dcapL i n ++ etaL i n) := by
  rw [etaImage_eq, capDiamond, Linear.smul_comp, Linear.comp_smul, smul_smul,
    mul_comm (entryCoeff (-t) _ _), entryCoeff_inverse t ht, one_smul,
    cl_comp (sChain_dcapL i n) (sChain_etaL i n)]

theorem matrixP₁ (t : k) (ht : t ^ 2 = -1) (ν : X) (i : I) (hh : 0 ≤ D.h i ν) :
    -(mixed (Sc := Sc) t ν i i ≫ mixedInverse t ν i i) +
      ∑ n ∈ Finset.range (D.h i ν).toNat, epsImage t ν i n ≫ cupDiamond t ν i n = 𝟙 _ := by
  simp only [mixed_same_comp t ht, eps_cupDiamond t ht]
  rw [cl_invP₁ Sc i ν hh, cl_nil]

theorem matrixP₂ (t : k) (ht : t ^ 2 = -1) (ν : X) (i : I) (hh : 0 ≤ D.h i ν) :
    mixedInverse (Sc := Sc) t ν i i ≫ mixed t ν i i = -𝟙 _ := by
  rw [mixed_same_comp' t ht, cl_invP₂ Sc i ν hh, cl_nil]

theorem matrixM₁ (t : k) (ht : t ^ 2 = -1) (ν : X) (i : I) (hh : D.h i ν ≤ 0) :
    -(mixedInverse (Sc := Sc) t ν i i ≫ mixed t ν i i) +
      ∑ n ∈ Finset.range (-D.h i ν).toNat, capDiamond t ν i n ≫ etaImage t ν i n = 𝟙 _ := by
  simp only [mixed_same_comp' t ht, capDiamond_eta t ht]
  rw [cl_invM₁ Sc i ν hh, cl_nil]

theorem matrixM₂ (t : k) (ht : t ^ 2 = -1) (ν : X) (i : I) (hh : D.h i ν ≤ 0) :
    mixed (Sc := Sc) t ν i i ≫ mixedInverse t ν i i = -𝟙 _ := by
  rw [mixed_same_comp t ht, cl_invM₂ Sc i ν hh, cl_nil]

theorem matrixP₃ (t : k) (ν : X) (i : I) (m : ℕ) (hm : (m : ℤ) < D.h i ν) :
    mixedInverse (Sc := Sc) t ν i i ≫ epsImage t ν i m = 0 := by
  rw [mixedInverse, epsImage_eq, Linear.smul_comp, Linear.comp_smul,
    cl_comp (sChain_lcrossL i i) (sChain_epsL i m), cl_invP₃ Sc i ν m hm,
    smul_zero, smul_zero]

theorem matrixP₄ (t : k) (ν : X) (i : I) (n : ℕ) (hn : (n : ℤ) < D.h i ν) :
    cupDiamond (Sc := Sc) t ν i n ≫ mixed t ν i i = 0 := by
  rw [cupDiamond, mixed_eq, Linear.smul_comp, Linear.comp_smul,
    cl_comp (sChain_dcupL i n) (sChain_sigmaL i i), cl_invP₄ Sc i ν n hn,
    smul_zero, smul_zero]

theorem matrixP₅ (t : k) (ht : t ^ 2 = -1) (ν : X) (i : I) (m n : ℕ)
    (hm : (m : ℤ) < D.h i ν) (hn : (n : ℤ) < D.h i ν) :
    cupDiamond (Sc := Sc) t ν i n ≫ epsImage t ν i m = if m = n then 𝟙 _ else 0 := by
  rw [cupDiamond, epsImage_eq, Linear.smul_comp, Linear.comp_smul,
    cl_comp (sChain_dcupL i n) (sChain_epsL i m), cl_invP₅ Sc i ν m n hm hn]
  split_ifs with h
  · subst m
    rw [smul_smul, mul_comm (entryCoeff (-t) _ _), entryCoeff_inverse t ht, one_smul, cl_nil]
  · rw [smul_zero, smul_zero]

theorem matrixM₃ (t : k) (ν : X) (i : I) (m : ℕ) (hm : (m : ℤ) < -D.h i ν) :
    etaImage (Sc := Sc) t ν i m ≫ mixedInverse t ν i i = 0 := by
  rw [mixedInverse, etaImage_eq, Linear.smul_comp, Linear.comp_smul,
    cl_comp (sChain_etaL i m) (sChain_lcrossL i i), cl_invM₃ Sc i ν m hm,
    smul_zero, smul_zero]

theorem matrixM₄ (t : k) (ν : X) (i : I) (n : ℕ) (hn : (n : ℤ) < -D.h i ν) :
    mixed (Sc := Sc) t ν i i ≫ capDiamond t ν i n = 0 := by
  rw [capDiamond, mixed_eq, Linear.smul_comp, Linear.comp_smul,
    cl_comp (sChain_sigmaL i i) (sChain_dcapL i n), cl_invM₄ Sc i ν n hn,
    smul_zero, smul_zero]

theorem matrixM₅ (t : k) (ht : t ^ 2 = -1) (ν : X) (i : I) (m n : ℕ)
    (hm : (m : ℤ) < -D.h i ν) (hn : (n : ℤ) < -D.h i ν) :
    etaImage (Sc := Sc) t ν i m ≫ capDiamond t ν i n = if m = n then 𝟙 _ else 0 := by
  rw [capDiamond, etaImage_eq, Linear.smul_comp, Linear.comp_smul,
    cl_comp (sChain_etaL i m) (sChain_dcapL i n), cl_invM₅ Sc i ν m n hm hn]
  split_ifs with h
  · subst m
    rw [smul_smul, entryCoeff_inverse t ht, one_smul, cl_nil]
  · rw [smul_zero, smul_zero]

theorem cupDiamond_zero (t : k) (ν : X) (i : I) (n : ℕ) (hn : D.h i ν ≤ n) :
    cupDiamond (Sc := Sc) t ν i n = 0 := by
  rw [cupDiamond, cl_dcupZero Sc i ν n hn, smul_zero]

theorem capDiamond_zero (t : k) (ν : X) (i : I) (n : ℕ) (hn : -D.h i ν ≤ n) :
    capDiamond (Sc := Sc) t ν i n = 0 := by
  rw [capDiamond, cl_dcapZero Sc i ν n hn, smul_zero]

end OddMath.SKM.RhoMixed
