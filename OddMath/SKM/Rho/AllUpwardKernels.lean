import OddMath.SKM.Rho.TriplePowers
import OddMath.SKM.Rho.SlideKernel

/-!
# All Upward Kernels for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoUpwardKernel
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords RhoEvaluator RhoCoefficients
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem rhoLin_braidEq (t : k) (ht : t^2 = -1) (μ : X) (i j : I) (hij : i ≠ j) :
    rhoLin (sy := sy) (hc := hc) t (wt D μ [up i,up j,up i]) μ rfl rfl
      (relation D Sc (.braidEq i j μ hij)) = 0 := by
  apply forget_injective (wt D μ [up i,up j,up i]) μ rfl rfl
  simp only [map_zero]
  change evalLin (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up i,up j,up i]) μ rfl rfl
    (relation D Sc (.braidEq i j μ hij)) = 0
  simp only [relation, map_sub, map_smul, map_sum, evalLin_dg, eval_braid_left,
    eval_braid_right, eval_braid_monomial, eval_braid_monomial_zero,
    crossLeft3_comp, crossRight3_comp]
  have H := crossing_braid_eq_raw (Sc := Sc) t ht (wt D μ [up i,up j,up i]) i j hij
  rw [smul_sub] at H
  simp only [Finset.smul_sum, smul_smul] at H
  apply sub_eq_zero.mpr
  apply sub_eq_iff_eq_add.mpr
  simpa only [mul_comm] using H.trans (add_comm _ _)

def IsUpward (r : Rel D) : Prop :=
  match r with
  | .quadEq .. | .quadZero .. | .quadNe .. | .slideL .. | .slideLEq .. |
    .slideR .. | .slideREq .. | .braid .. | .braidEq .. => True
  | _ => False

theorem rhoLin_upward (t : k) (ht : t^2 = -1) (r : Rel D) (hr : IsUpward r)
    (hcod : wt D r.ν r.cod = wt D r.ν r.dom) :
    rhoLin (sy := sy) (hc := hc) t (wt D r.ν r.dom) r.ν rfl hcod (relation D Sc r) = 0 := by
  cases r with
  | quadEq i μ => exact rhoLin_quadEq t μ i
  | quadZero i j μ hij hd => exact rhoLin_quadZero t ht μ i j hij hd
  | quadNe i j μ hij hd => exact rhoLin_quadNe t ht μ i j hij hd
  | slideL i j μ hij => exact rhoLin_slideL t μ i j hij
  | slideLEq i μ => exact rhoLin_slideLEq t ht μ i
  | slideR i j μ hij => exact rhoLin_slideR t μ i j hij
  | slideREq i μ => exact rhoLin_slideREq t ht μ i
  | braid i j a μ hia => exact rhoLin_braid t μ i j a hia
  | braidEq i j μ hij => exact rhoLin_braidEq t ht μ i j hij
  | _ => contradiction

end OddMath.SKM.RhoUpwardKernel
