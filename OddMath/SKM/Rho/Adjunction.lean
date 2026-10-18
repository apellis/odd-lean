import OddMath.SKM.Rho.RawFormula

/-!
# Adjunction for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoInversionKernel
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords RhoEvaluator
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem loopE_image (t : k) (μ : X) (i : I) :
    rhoRaw (sy := sy) (hc := hc) t (wt D μ [up i]) μ
      [([up i], Shape.cup i, []), ([], Shape.cap i, [up i])] rfl rfl
      (by simp [SChain, Shape.dom, Shape.cod]) = 𝟙 _ := by
  have H := raw_formula (sy := sy) (hc := hc) (Sc := Sc) t (wt D μ [up i]) μ
    [([up i], Shape.cup i, []), ([], Shape.cap i, [up i])] (s := [up i]) (r := [up i]) rfl rfl
    (by simp [SChain, Shape.dom, Shape.cod])
  have e : imageCoeff (D := D) t [([up i], Shape.cup i, []), ([], Shape.cap i, [up i])] •
      cl D Sc (wt D μ [up i]) [dn i] [dn i]
        (imageLayers [([up i], Shape.cup i, []), ([], Shape.cap i, [up i])]) =
      𝟙 ((pres D Sc).obj (ob D (wt D μ [up i]) [dn i])) := by
    simp only [imageCoeff, RhoGenerators.coeff, mul_one, one_smul]
    change cl D Sc (wt D μ [up i]) [dn i] [dn i]
      [([], Shape.cup i, [dn i]), ([dn i], Shape.cap i, [])] = _
    rw [cl_zigF, cl_nil]
  exact eq_of_heq (H.trans ((heq_of_eq e).trans
    (id_heq (congrArg (pres D Sc).obj
      (at_obj (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [up i]) μ [up i] rfl))).symm))

theorem loopF_image (t : k) (μ : X) (i : I) :
    rhoRaw (sy := sy) (hc := hc) t (wt D μ [dn i]) μ
      [([], Shape.cup i, [dn i]), ([dn i], Shape.cap i, [])] rfl rfl
      (by simp [SChain, Shape.dom, Shape.cod]) = 𝟙 _ := by
  have H := raw_formula (sy := sy) (hc := hc) (Sc := Sc) t (wt D μ [dn i]) μ
    [([], Shape.cup i, [dn i]), ([dn i], Shape.cap i, [])] (s := [dn i]) (r := [dn i]) rfl rfl
    (by simp [SChain, Shape.dom, Shape.cod])
  have e : imageCoeff (D := D) t [([], Shape.cup i, [dn i]), ([dn i], Shape.cap i, [])] •
      cl D Sc (wt D μ [dn i]) [up i] [up i]
        (imageLayers [([], Shape.cup i, [dn i]), ([dn i], Shape.cap i, [])]) =
      𝟙 ((pres D Sc).obj (ob D (wt D μ [dn i]) [up i])) := by
    simp only [imageCoeff, RhoGenerators.coeff, mul_one, one_smul]
    change cl D Sc (wt D μ [dn i]) [up i] [up i]
      [([up i], Shape.cup i, []), ([], Shape.cap i, [up i])] = _
    rw [cl_zigE, cl_nil]
  exact eq_of_heq (H.trans ((heq_of_eq e).trans
    (id_heq (congrArg (pres D Sc).obj
      (at_obj (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [dn i]) μ [dn i] rfl))).symm))

theorem kernel_zigE (t : k) (μ : X) (i : I) :
    rhoLin (sy := sy) (hc := hc) t (wt D μ [up i]) μ rfl rfl
      (relation D Sc (.zigE i μ)) = 0 := by
  change rhoLin (sy := sy) (hc := hc) t (wt D μ [up i]) μ (s := [up i]) (r := [up i]) rfl rfl
    (dg D μ (t := [up i]) (t' := [up i]) [([up i], Shape.cup i, []), ([], Shape.cap i, [up i])]
      (by simp [SChain, Shape.dom, Shape.cod]) - idg D μ [up i]) = 0
  rw [map_sub, rhoLin_dg, rhoLin_idg, loopE_image, sub_self]

theorem kernel_zigF (t : k) (μ : X) (i : I) :
    rhoLin (sy := sy) (hc := hc) t (wt D μ [dn i]) μ rfl rfl
      (relation D Sc (.zigF i μ)) = 0 := by
  change rhoLin (sy := sy) (hc := hc) t (wt D μ [dn i]) μ (s := [dn i]) (r := [dn i]) rfl rfl
    (dg D μ (t := [dn i]) (t' := [dn i]) [([], Shape.cup i, [dn i]), ([dn i], Shape.cap i, [])]
      (by simp [SChain, Shape.dom, Shape.cod]) - idg D μ [dn i]) = 0
  rw [map_sub, rhoLin_dg, rhoLin_idg, loopF_image, sub_self]

end OddMath.SKM.RhoInversionKernel
