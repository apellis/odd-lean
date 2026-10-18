import OddMath.SKM.Rho.Coefficients
import OddMath.SKM.Lemma33

/-!
# Upward for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.SKM.RhoCoefficients
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem correctedCrossing_eq (t : k) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i,j]) = ν) :
    correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h =
      psiCoeff t (D.parity i * D.parity j) •
        cl D Sc ν [dn j,dn i] [dn i,dn j] (dcrossL j i) := by
  simp only [correctedCrossing, rhoCross, smul_smul, crossing_coefficient]

theorem coeff_sq (t : k) (ht : t ^ 2 = -1) (p : ZMod 2) :
    psiCoeff t p * psiCoeff t p = zsign k p := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [psiCoeff, zsign, ← pow_two, ht]

theorem crossing_equal_slide_right (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I)
    (h : wt D μ (ups [i,i]) = ν) :
    correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i i h ≫
        rhoDotLeft t ν μ i i h =
      zsign k (D.parity i * D.parity i) •
        (rhoDotRight t ν μ i i h ≫ correctedCrossing t ν μ i i h) + 𝟙 _ := by
  change (zsign k (D.parity i * D.parity i) •
    (psiCoeff (-t) (D.parity i * D.parity i) • cl D Sc ν [dn i,dn i] [dn i,dn i] (dcrossL i i))) ≫
    (psiCoeff t (D.parity i) • cl D Sc ν [dn i,dn i] [dn i,dn i]
      ((ddotL i).map (whL [dn i] []))) =
    zsign k (D.parity i * D.parity i) •
      ((psiCoeff t (D.parity i) • cl D Sc ν [dn i,dn i] [dn i,dn i]
        ((ddotL i).map (whL [] [dn i]))) ≫
        (zsign k (D.parity i * D.parity i) •
          (psiCoeff (-t) (D.parity i * D.parity i) • cl D Sc ν [dn i,dn i] [dn i,dn i] (dcrossL i i)))) +
        𝟙 ((pres D Sc).obj (ob D ν [dn i,dn i]))
  simp only [smul_smul, crossing_coefficient]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, zmod2_mul_self', coeff_sq t ht,
    zsign_mul_self, one_smul]
  have hl : SChain [dn i,dn i] ((ddotL i).map (whL [] [dn i])) [dn i,dn i] :=
    (sChain_ddotL i).wh [] [dn i] rfl rfl
  have hr : SChain [dn i,dn i] ((ddotL i).map (whL [dn i] [])) [dn i,dn i] :=
    (sChain_ddotL i).wh [dn i] [] rfl rfl
  rw [cl_comp (D := D) (Sc := Sc) (μ := ν) (sChain_dcrossL i i) hr,
    cl_comp (D := D) (Sc := Sc) (μ := ν) hl (sChain_dcrossL i i)]
  have H := lemma31_eq5_eq Sc i ν 1
  simp [ddotsL, cl_nil, zmod2_mul_self', zsign_zero] at H
  exact (sub_eq_iff_eq_add.mp H).trans (add_comm _ _)

theorem crossing_equal_quadratic (t : k) (ν μ : X) (i : I)
    (h : wt D μ (ups [i,i]) = ν) :
    correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i i h ≫
      correctedCrossing t ν μ i i h = 0 := by
  rw [crossing_cross_comp, rhoCross_sq]

theorem crossing_mem_parity (t : k) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i,j]) = ν) :
    correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ∈
      parity (R := k) _ _ (D.parity i * D.parity j) :=
  Submodule.smul_mem _ _ (rhoCross_mem_parity t ν μ i j h)

theorem crossing_mem_degree (t : k) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i,j]) = ν) :
    correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ∈
      GradedSupercategory.degree (R := k) _ _ (sy.d i * D.d i j) :=
  Submodule.smul_mem _ _ (rhoCross_mem_degree t ν μ i j h)

end OddMath.SKM.RhoCoefficients
