import OddMath.SKM.Rho.PrintedSlideConstraint

/-!
# Coefficients for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
The corrected crossing coefficient is +t for two odd colours, while the odd dot
coefficient remains +t. The F-image has added parity shift zero.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.SKM.RhoCoefficients
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

private theorem swap_weight (μ : X) (i j : I) :
    wt D μ (ups [i,j]) = wt D μ (ups [j,i]) := by
  simp [ups, wt, sh, add_comm, add_left_comm, add_assoc]

theorem crossing_coefficient (t : k) (p : ZMod 2) :
    zsign k p * psiCoeff (-t) p = psiCoeff t p := by
  rcases parity_eq_zero_or_one p with h | h <;> simp [h, psiCoeff, zsign]

def correctedCrossing (t : k) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i,j]) = ν) :=
  zsign k (D.parity i * D.parity j) •
    rhoCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h

theorem crossing_equal_slide (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I)
    (h : wt D μ (ups [i,i]) = ν) :
    rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i i h ≫
        correctedCrossing t ν μ i i h =
      zsign k (D.parity i * D.parity i) •
        (correctedCrossing t ν μ i i h ≫ rhoDotRight t ν μ i i h) + 𝟙 _ := by
  simpa only [correctedCrossing, zmod2_mul_self', zsign_mul_self, one_smul] using
    crossing_scalar_residual (Sc := Sc) (sy := sy) (hc := hc)
      (zsign k (D.parity i * D.parity i)) t ht ν μ i h

theorem crossing_cross_comp (t : k) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i,j]) = ν) :
    correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ≫
      correctedCrossing t ν μ j i ((swap_weight μ i j).symm.trans h) =
    rhoCross t ν μ i j h ≫ rhoCross t ν μ j i ((swap_weight μ i j).symm.trans h) := by
  simp only [correctedCrossing, Linear.smul_comp, Linear.comp_smul,
    smul_smul, mul_comm (D.parity j) (D.parity i), zsign_mul_self, one_smul]

theorem crossing_disconnected (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i,j]) = ν) (hij : i ≠ j) (hd : D.d i j = 0) :
    correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ≫
      correctedCrossing t ν μ j i ((swap_weight μ i j).symm.trans h) = (Sc.t i j : k) • 𝟙 _ := by
  rw [crossing_cross_comp, rhoCross_quadZero t ht ν μ i j h hij hd]

theorem crossing_distinct_slide (t : k) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i,j]) = ν) (hij : i ≠ j) :
    rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ≫
        correctedCrossing t ν μ i j h =
      zsign k (D.parity i * D.parity j) •
        (correctedCrossing t ν μ i j h ≫
          rhoDotRight t ν μ j i ((swap_weight μ i j).symm.trans h)) := by
  simpa only [correctedCrossing, Linear.smul_comp, Linear.comp_smul] using
    congrArg (zsign k (D.parity i * D.parity j) • ·)
      (rho_slideL (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h hij)

theorem crossing_distinct_slide_right (t : k) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i,j]) = ν) (hij : i ≠ j) :
    correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ≫
        rhoDotLeft t ν μ j i ((swap_weight μ i j).symm.trans h) =
      zsign k (D.parity i * D.parity j) •
        (rhoDotRight t ν μ i j h ≫ correctedCrossing t ν μ i j h) := by
  simpa only [correctedCrossing, Linear.smul_comp, Linear.comp_smul] using
    congrArg (zsign k (D.parity i * D.parity j) • ·)
      (rho_slideR (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h hij)

end OddMath.SKM.RhoCoefficients
