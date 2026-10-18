import OddMath.SKM.Rho.LayerComparison

/-!
# Quadratic Kernel for ρ

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

theorem rhoLin_quadEq (t : k) (μ : X) (i : I) :
    rhoLin (sy := sy) (hc := hc) t (wt D μ [up i,up i]) μ rfl rfl
      (relation D Sc (.quadEq i μ)) = 0 := by
  apply forget_injective (wt D μ [up i,up i]) μ rfl rfl
  simp only [map_zero, relation]
  erw [rhoLin_dg]
  erw [rhoRaw_append t _ μ _ _ rfl rfl rfl
    (show SChain [up i,up i] (crossL [] i i []) [up i,up i] by simp [crossL, SChain, Shape.dom, Shape.cod])
    (show SChain [up i,up i] (crossL [] i i []) [up i,up i] by simp [crossL, SChain, Shape.dom, Shape.cod])]
  erw [forget_comp _ _ rfl rfl rfl, bare_cross]
  have H := crossing_equal_quadratic (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up i,up i]) μ i rfl
  erw [correctedCrossing_eq] at H
  exact H

theorem rhoLin_quadZero (t : k) (ht : t^2 = -1) (μ : X) (i j : I)
    (hij : i ≠ j) (hd : D.d i j = 0) :
    rhoLin (sy := sy) (hc := hc) t (wt D μ [up i,up j]) μ rfl rfl
      (relation D Sc (.quadZero i j μ hij hd)) = 0 := by
  have hj : wt D μ [up j,up i] = wt D μ [up i,up j] := by simp [wt, sh, add_comm, add_left_comm, add_assoc]
  apply forget_injective (wt D μ [up i,up j]) μ rfl rfl
  simp only [relation, map_sub, map_smul, map_zero]
  erw [rhoLin_dg, rhoLin_idg, forget_id]
  erw [rhoRaw_append t _ μ _ _ rfl hj rfl
    (show SChain [up i,up j] (crossL [] i j []) [up j,up i] by simp [crossL, SChain, Shape.dom, Shape.cod])
    (show SChain [up j,up i] (crossL [] j i []) [up i,up j] by simp [crossL, SChain, Shape.dom, Shape.cod])]
  erw [forget_comp _ _ rfl hj rfl, bare_cross, bare_cross]
  have H := crossing_disconnected (Sc := Sc) (sy := sy) (hc := hc) t ht (wt D μ [up i,up j]) μ i j rfl hij hd
  simp only [correctedCrossing_eq] at H
  exact sub_eq_zero.mpr H

end OddMath.SKM.RhoUpwardKernel
