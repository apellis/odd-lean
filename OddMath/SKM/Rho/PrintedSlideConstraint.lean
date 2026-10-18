import OddMath.SKM.RhoGenerators

/-!
# Printed Slide Constraint for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
The printed odd–odd crossing coefficient −t forces the constraint id + id = 0
if the equal-colour dot-slide relation is preserved. No nonzero identity witness is asserted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.SKM.RhoCoefficients
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem residual (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I)
    (h : wt D μ (ups [i, i]) = ν) :
    rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i i h ≫ rhoCross t ν μ i i h =
      zsign k (D.parity i * D.parity i) •
        (rhoCross t ν μ i i h ≫ rhoDotRight t ν μ i i h) +
          zsign k (D.parity i) • 𝟙 _ := by
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h0 | h1
    · simp [h0]
    · simp [h1]
  have hm : psiCoeff (-t) (D.parity i * D.parity i) * psiCoeff t (D.parity i) = 1 := by
    rw [hp]
    rcases parity_eq_zero_or_one (D.parity i) with h0 | h1
    · simp [psiCoeff, h0]
    · simp only [h1, psiCoeff_one, neg_mul]
      rw [← pow_two, ht, neg_neg]
  change (psiCoeff t (D.parity i) • cl D Sc ν [dn i, dn i] [dn i, dn i]
    ((ddotL i).map (whL [dn i] []))) ≫
    (psiCoeff (-t) (D.parity i * D.parity i) • cl D Sc ν [dn i, dn i] [dn i, dn i] (dcrossL i i)) =
    zsign k (D.parity i * D.parity i) •
      ((psiCoeff (-t) (D.parity i * D.parity i) • cl D Sc ν [dn i, dn i] [dn i, dn i] (dcrossL i i)) ≫
        (psiCoeff t (D.parity i) • cl D Sc ν [dn i, dn i] [dn i, dn i]
          ((ddotL i).map (whL [] [dn i])))) +
            zsign k (D.parity i) • 𝟙 ((pres D Sc).obj (ob D ν [dn i, dn i]))
  simp only [Linear.smul_comp, Linear.comp_smul]
  rw [smul_smul, hm, one_smul]
  conv_rhs => arg 1; arg 2; rw [smul_smul, mul_comm, hm, one_smul]
  have hl : SChain [dn i, dn i] ((ddotL i).map (whL [] [dn i])) [dn i, dn i] :=
    (sChain_ddotL i).wh [] [dn i] rfl rfl
  have hr : SChain [dn i, dn i] ((ddotL i).map (whL [dn i] [])) [dn i, dn i] :=
    (sChain_ddotL i).wh [dn i] [] rfl rfl
  rw [cl_comp (D := D) (Sc := Sc) (μ := ν) hr (sChain_dcrossL i i),
    cl_comp (D := D) (Sc := Sc) (μ := ν) (sChain_dcrossL i i) hl, hp]
  have H := lemma31_eq6_eq Sc i ν 1
  simp [ddotsL, cl_nil] at H
  have H' := congrArg (zsign k (D.parity i) • ·) H
  have hz : zsign k 0 = 1 := by simp [zsign]
  simp only [smul_sub, smul_smul, hp, hz, zsign_mul_self, one_smul] at H'
  exact (sub_eq_iff_eq_add.mp H').trans (add_comm _ _)

theorem odd_printed_relation_forces_two_id (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I)
    (h : wt D μ (ups [i,i]) = ν) (hi : D.parity i = 1)
    (hs : rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i i h ≫ rhoCross t ν μ i i h =
      zsign k (D.parity i * D.parity i) •
        (rhoCross t ν μ i i h ≫ rhoDotRight t ν μ i i h) + 𝟙 _) :
    (𝟙 (rhoUpAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [i,i] h)) + 𝟙 _ = 0 := by
  have H := residual (Sc := Sc) (sy := sy) (hc := hc) t ht ν μ i h
  have E := H.symm.trans hs
  have E' := add_left_cancel E
  have hz : zsign k 1 = -1 := by simp [zsign]
  simp only [hi, hz, neg_one_smul] at E'
  calc
    𝟙 _ + 𝟙 _ = -𝟙 _ + 𝟙 _ := by rw [E']
    _ = 0 := neg_add_cancel _

theorem crossing_scalar_residual (c t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I)
    (h : wt D μ (ups [i,i]) = ν) :
    rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i i h ≫ (c • rhoCross t ν μ i i h) =
      zsign k (D.parity i * D.parity i) •
        ((c • rhoCross t ν μ i i h) ≫ rhoDotRight t ν μ i i h) +
          (c * zsign k (D.parity i)) • 𝟙 _ := by
  rw [Linear.comp_smul, Linear.smul_comp, residual t ht, smul_add, smul_smul]
  rw [smul_comm (zsign k _) c]
  simp only [smul_smul]

end OddMath.SKM.RhoCoefficients
