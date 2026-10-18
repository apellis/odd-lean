import OddMath.SKM.Rho.PairPowers

/-!
# Connected Kernel for ρ

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

def evalLin (t : k) (ν μ : X) {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν) :
    LinDiagram k (ob D μ s) (ob D μ r) →ₗ[k]
      ((pres D Sc).obj (ob D ν (rhoWord s)) ⟶ (pres D Sc).obj (ob D ν (rhoWord r))) :=
  (forget (Sc := Sc) (sy := sy) (hc := hc) ν μ hs hr).comp (rhoLin t ν μ hs hr)

theorem evalLin_dg (t : k) (ν μ : X) (L : List (LayerData I)) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (h : SChain s L r) :
    evalLin (Sc := Sc) (sy := sy) (hc := hc) t ν μ hs hr (dg D μ L h) =
      eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ L hs hr h := forget_dg t ν μ L hs hr h

theorem rhoLin_quadNe (t : k) (ht : t^2 = -1) (μ : X) (i j : I)
    (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    rhoLin (sy := sy) (hc := hc) t (wt D μ [up i,up j]) μ rfl rfl
      (relation D Sc (.quadNe i j μ hij hd)) = 0 := by
  apply forget_injective (wt D μ [up i,up j]) μ rfl rfl
  simp only [map_zero]
  change evalLin (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up i,up j]) μ rfl rfl
    (relation D Sc (.quadNe i j μ hij hd)) = 0
  simp only [relation, map_sub, map_smul, map_sum]
  simp only [evalLin_dg, eval_xx, eval_dots_left, eval_dots_right, eval_pair_monomial]
  have H := crossing_connected_quadratic (Sc := Sc) (sy := sy) (hc := hc) t ht (wt D μ [up i,up j]) μ i j rfl hij hd
  exact sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr (sub_eq_iff_eq_add.mpr (H.trans (by abel))))

end OddMath.SKM.RhoUpwardKernel
