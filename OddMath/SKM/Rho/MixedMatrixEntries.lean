import OddMath.SKM.Rho.Whisker

/-!
# Mixed Matrix Entries for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoMixedMatrixEntries
open CategoryTheory StringDiagrams Supercategory RhoMixed
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem same_shift (μ : X) (i : I) : mixedShift (sy := sy) μ i i = 0 := by
  rw [mixedShift, D.d_self]
  ring

theorem same_EF_shift (μ : X) (i : I) :
    (EF (Sc := Sc) (sy := sy) (hc := hc) μ i i).obj.shift = 0 := by
  rw [EF_shift, same_shift]

theorem same_FE_shift (μ : X) (i : I) :
    (FE (Sc := Sc) (sy := sy) (hc := hc) μ i i).obj.shift = 0 := by
  rw [FE_shift, same_shift]

theorem same_sigma (t : k) (μ : X) (i : I) :
    HEq (sigmaImage (Sc := Sc) (sy := sy) (hc := hc) t μ i i) (mixed (Sc := Sc) t μ i i) := by
  rw [sigmaImage_eq_mixed]
  have h : wt D μ [up i,dn i] = μ := by simp [wt, sh]
  rw [h]

def S (t : k) (μ : X) (i : I) :=
  cast (type_eq_of_heq (same_sigma (Sc := Sc) (sy := sy) (hc := hc) t μ i))
    (sigmaImage (Sc := Sc) (sy := sy) (hc := hc) t μ i i)

private theorem cast_of_heq {α β : Sort u} {a : α} {b : β} (h : HEq a b) :
    cast (type_eq_of_heq h) a = b := by cases h; rfl

theorem S_eq (t : k) (μ : X) (i : I) :
    S (Sc := Sc) (sy := sy) (hc := hc) t μ i = mixed t μ i i :=
  cast_of_heq (same_sigma (Sc := Sc) (sy := sy) (hc := hc) t μ i)

theorem matrix_P₁ (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (hh : 0 ≤ D.h i μ) :
    -(S (Sc := Sc) (sy := sy) (hc := hc) t μ i ≫ mixedInverse t μ i i) +
      ∑ n ∈ Finset.range (D.h i μ).toNat, epsImage t μ i n ≫ cupDiamond t μ i n = 𝟙 _ := by
  rw [S_eq, matrixP₁ t ht μ i hh]

theorem matrix_M₁ (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (hh : D.h i μ ≤ 0) :
    -(mixedInverse (Sc := Sc) t μ i i ≫ S (sy := sy) (hc := hc) t μ i) +
      ∑ n ∈ Finset.range (-D.h i μ).toNat, capDiamond t μ i n ≫ etaImage t μ i n = 𝟙 _ := by
  rw [S_eq, matrixM₁ t ht μ i hh]

example (t : k) (ht : t ^ 2 = -1) (μ : X) (i j : I) (hij : i ≠ j) :
    sigmaImage (Sc := Sc) (sy := sy) (hc := hc) t μ i j ≫
      mixedInverse t (wt D μ [up j,dn i]) i j = 𝟙 _ :=
  sigmaImage_invNe₁ t ht μ i j hij

end OddMath.SKM.RhoMixedMatrixEntries
