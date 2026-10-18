import OddMath.SKM.Rho.Dotted
import OddMath.SKM.Rho.MixedMatrixEntries

/-!
# Dotted Matrix Entries for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoDottedMatrixEntries
open CategoryTheory StringDiagrams Supercategory RhoMixed RhoDotted RhoMixedMatrixEntries
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

def E (t : k) (μ : X) (i : I) (n : ℕ) :
    (pres D Sc).obj (ob D μ [up i,dn i]) ⟶ (pres D Sc).obj (ob D μ []) :=
  dottedCap (Sc := Sc) (sy := sy) (hc := hc) t μ i n

def N (t : k) (μ : X) (i : I) (n : ℕ) :
    (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [dn i,up i]) :=
  dottedCup (Sc := Sc) (sy := sy) (hc := hc) t μ i n

theorem E_eq (t : k) (μ : X) (i : I) (n : ℕ) :
    E (Sc := Sc) (sy := sy) (hc := hc) t μ i n = epsImage t μ i n :=
  dottedCap_eq_raw t μ i n

theorem N_eq (t : k) (μ : X) (i : I) (n : ℕ) :
    N (Sc := Sc) (sy := sy) (hc := hc) t μ i n = etaImage t μ i n :=
  dottedCup_eq_raw t μ i n

theorem boundary_shifts (μ : X) (i : I) :
    (rhoE (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [dn i]) i ≫ rhoF μ i).par = 0 ∧
    (rhoE (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [dn i]) i ≫ rhoF μ i).obj.shift = 0 ∧
    (rhoF (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [up i]) i ≫ rhoE μ i).par = 0 ∧
    (rhoF (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [up i]) i ≫ rhoE μ i).obj.shift = 0 :=
  ⟨RhoParity.EF_par 0 μ i, RhoParity.EF_shift 0 μ i,
    RhoParity.FE_par 0 μ i, RhoParity.FE_shift 0 μ i⟩

theorem P₁ (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (hh : 0 ≤ D.h i μ) :
    -(S (Sc := Sc) (sy := sy) (hc := hc) t μ i ≫ mixedInverse t μ i i) +
      ∑ n ∈ Finset.range (D.h i μ).toNat,
        E (sy := sy) (hc := hc) t μ i n ≫ cupDiamond t μ i n = 𝟙 _ := by
  simp only [S_eq, E_eq]
  exact matrixP₁ t ht μ i hh

theorem P₂ (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (hh : 0 ≤ D.h i μ) :
    mixedInverse (Sc := Sc) t μ i i ≫ S (sy := sy) (hc := hc) t μ i = -𝟙 _ := by
  rw [S_eq, matrixP₂ t ht μ i hh]

theorem P₃ (t : k) (μ : X) (i : I) (m : ℕ) (hm : (m : ℤ) < D.h i μ) :
    mixedInverse (Sc := Sc) t μ i i ≫ E (sy := sy) (hc := hc) t μ i m = 0 := by
  rw [E_eq, matrixP₃ t μ i m hm]

theorem P₄ (t : k) (μ : X) (i : I) (n : ℕ) (hn : (n : ℤ) < D.h i μ) :
    cupDiamond (Sc := Sc) t μ i n ≫ S (sy := sy) (hc := hc) t μ i = 0 := by
  rw [S_eq, matrixP₄ t μ i n hn]

theorem P₅ (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (m n : ℕ)
    (hm : (m : ℤ) < D.h i μ) (hn : (n : ℤ) < D.h i μ) :
    cupDiamond (Sc := Sc) t μ i n ≫ E (sy := sy) (hc := hc) t μ i m =
      if m = n then 𝟙 _ else 0 := by
  rw [E_eq, matrixP₅ t ht μ i m n hm hn]

theorem M₁ (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (hh : D.h i μ ≤ 0) :
    -(mixedInverse (Sc := Sc) t μ i i ≫ S (sy := sy) (hc := hc) t μ i) +
      ∑ n ∈ Finset.range (-D.h i μ).toNat,
        capDiamond t μ i n ≫ N (sy := sy) (hc := hc) t μ i n = 𝟙 _ := by
  simp only [S_eq, N_eq]
  exact matrixM₁ t ht μ i hh

theorem M₂ (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (hh : D.h i μ ≤ 0) :
    S (Sc := Sc) (sy := sy) (hc := hc) t μ i ≫ mixedInverse t μ i i = -𝟙 _ := by
  rw [S_eq, matrixM₂ t ht μ i hh]

theorem M₃ (t : k) (μ : X) (i : I) (m : ℕ) (hm : (m : ℤ) < -D.h i μ) :
    N (Sc := Sc) (sy := sy) (hc := hc) t μ i m ≫ mixedInverse t μ i i = 0 := by
  rw [N_eq, matrixM₃ t μ i m hm]

theorem M₄ (t : k) (μ : X) (i : I) (n : ℕ) (hn : (n : ℤ) < -D.h i μ) :
    S (Sc := Sc) (sy := sy) (hc := hc) t μ i ≫ capDiamond t μ i n = 0 := by
  rw [S_eq, matrixM₄ t μ i n hn]

theorem M₅ (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (m n : ℕ)
    (hm : (m : ℤ) < -D.h i μ) (hn : (n : ℤ) < -D.h i μ) :
    N (Sc := Sc) (sy := sy) (hc := hc) t μ i m ≫ capDiamond t μ i n =
      if m = n then 𝟙 _ else 0 := by
  rw [N_eq, matrixM₅ t ht μ i m n hm hn]

theorem cup_zero (t : k) (μ : X) (i : I) (n : ℕ) (hn : D.h i μ ≤ n) :
    cupDiamond (Sc := Sc) t μ i n = 0 := cupDiamond_zero t μ i n hn

theorem cap_zero (t : k) (μ : X) (i : I) (n : ℕ) (hn : -D.h i μ ≤ n) :
    capDiamond (Sc := Sc) t μ i n = 0 := capDiamond_zero t μ i n hn

end OddMath.SKM.RhoDottedMatrixEntries
