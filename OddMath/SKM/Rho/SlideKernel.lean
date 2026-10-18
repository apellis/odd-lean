import OddMath.SKM.Rho.PairWords
import OddMath.SKM.Rho.QuadraticKernel

/-!
# Slide Kernel for ρ

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

theorem rhoLin_slideL (t : k) (μ : X) (i j : I) (hij : i ≠ j) :
    rhoLin (sy := sy) (hc := hc) t (wt D μ [up i,up j]) μ rfl
      ((show wt D μ [up j,up i] = wt D μ [up i,up j] by simp [wt, sh, add_comm, add_left_comm, add_assoc]))
      (relation D Sc (.slideL i j μ hij)) = 0 := by
  have hj : wt D μ [up j,up i] = wt D μ [up i,up j] := by simp [wt, sh, add_comm, add_left_comm, add_assoc]
  apply forget_injective (wt D μ [up i,up j]) μ rfl hj
  simp only [relation, map_sub, map_smul, map_zero]
  erw [forget_dg, forget_dg]
  erw [eval_lx, eval_xr]
  have H := crossing_distinct_slide (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up i,up j]) μ i j rfl hij
  exact sub_eq_zero.mpr H

theorem rhoLin_slideLEq (t : k) (ht : t^2 = -1) (μ : X) (i : I) :
    rhoLin (sy := sy) (hc := hc) t (wt D μ [up i,up i]) μ rfl
      (rfl)
      (relation D Sc (.slideLEq i μ)) = 0 := by
  apply forget_injective (wt D μ [up i,up i]) μ rfl rfl
  simp only [relation, map_sub, map_smul, map_zero]
  erw [forget_dg, forget_dg, forget_idg]
  have H := crossing_equal_slide (Sc := Sc) (sy := sy) (hc := hc) t ht (wt D μ [up i,up i]) μ i rfl
  exact (congrArg₂ (fun a b => a - zsign k (D.parity i * D.parity i) • b -
    𝟙 ((pres D Sc).obj (ob D (wt D μ [up i,up i]) [dn i,dn i])))
    (eval_lx (Sc := Sc) (sy := sy) (hc := hc) t _ μ i i rfl rfl)
    (eval_xr (Sc := Sc) (sy := sy) (hc := hc) t _ μ i i rfl rfl)).trans
      (sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr (H.trans (add_comm _ _))))

theorem rhoLin_slideR (t : k) (μ : X) (i j : I) (hij : i ≠ j) :
    rhoLin (sy := sy) (hc := hc) t (wt D μ [up i,up j]) μ rfl
      ((show wt D μ [up j,up i] = wt D μ [up i,up j] by simp [wt, sh, add_comm, add_left_comm, add_assoc]))
      (relation D Sc (.slideR i j μ hij)) = 0 := by
  have hj : wt D μ [up j,up i] = wt D μ [up i,up j] := by simp [wt, sh, add_comm, add_left_comm, add_assoc]
  apply forget_injective (wt D μ [up i,up j]) μ rfl hj
  simp only [relation, map_sub, map_smul, map_zero]
  erw [forget_dg, forget_dg]
  erw [eval_xl, eval_rx]
  have H := crossing_distinct_slide_right (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up i,up j]) μ i j rfl hij
  exact sub_eq_zero.mpr H

theorem rhoLin_slideREq (t : k) (ht : t^2 = -1) (μ : X) (i : I) :
    rhoLin (sy := sy) (hc := hc) t (wt D μ [up i,up i]) μ rfl
      (rfl)
      (relation D Sc (.slideREq i μ)) = 0 := by
  apply forget_injective (wt D μ [up i,up i]) μ rfl rfl
  simp only [relation, map_sub, map_smul, map_zero]
  erw [forget_dg, forget_dg, forget_idg]
  have H := crossing_equal_slide_right (Sc := Sc) (sy := sy) (hc := hc) t ht (wt D μ [up i,up i]) μ i rfl
  exact (congrArg₂ (fun a b => a - zsign k (D.parity i * D.parity i) • b -
    𝟙 ((pres D Sc).obj (ob D (wt D μ [up i,up i]) [dn i,dn i])))
    (eval_xl (Sc := Sc) (sy := sy) (hc := hc) t _ μ i i rfl rfl)
    (eval_rx (Sc := Sc) (sy := sy) (hc := hc) t _ μ i i rfl rfl)).trans
      (sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr (H.trans (add_comm _ _))))

end OddMath.SKM.RhoUpwardKernel
