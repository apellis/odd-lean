import OddMath.SKM.Rho.UpwardWords
import OddMath.SKM.Rho.ConnectedKernel

/-!
# Braid Kernel for ρ

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

theorem eval_cross_left3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ [up i,up j,up a] = ν)
    (h' : wt D μ [up j,up i,up a] = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (crossL [] i j [up a]) h h' ⟨rfl,rfl⟩ =
      crossLeft3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h := cross_left3 t ν μ i j a h

theorem eval_cross_right3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ [up i,up j,up a] = ν)
    (h' : wt D μ [up i,up a,up j] = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (crossL [up i] j a []) h h' ⟨rfl,rfl⟩ =
      crossRight3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h := cross_right3 t ν μ i j a h

theorem eval_append3 (t : k) (ν μ : X) (L M N : List (LayerData I)) {s r q z : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hq : wt D μ q = ν) (hz : wt D μ z = ν)
    (hL : SChain s L r) (hM : SChain r M q) (hN : SChain q N z) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (L ++ M ++ N) hs hz ((hL.append hM).append hN) =
      eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ L hs hr hL ≫
        eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ M hr hq hM ≫
          eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ N hq hz hN := by
  calc
    _ = eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (L ++ M) hs hq (hL.append hM) ≫
        eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ N hq hz hN := eval_append t ν μ _ _ hs hq hz _ _
    _ = _ := by rw [eval_append t ν μ L M hs hr hq hL hM, Category.assoc]

theorem eval_braid_left (t : k) (ν μ : X) (i j a : I) (h : wt D μ [up i,up j,up a] = ν)
    (h' : wt D μ [up a,up j,up i] = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ
      (crossL [] i j [up a] ++ crossL [up j] i a [] ++ crossL [] j a [up i]) h h'
      (by simp [crossL, Shape.dom, Shape.cod]) =
      crossLeft3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h ≫
        crossRight3 t ν μ j i a ((wt_swap_left3 μ i j a).trans h) ≫
        crossLeft3 t ν μ j a i ((wt_swap_right3 μ j i a).trans ((wt_swap_left3 μ i j a).trans h)) := by
  exact (eval_append3 t ν μ _ _ _ h ((wt_swap_left3 μ i j a).trans h)
    ((wt_swap_right3 μ j i a).trans ((wt_swap_left3 μ i j a).trans h)) h'
    (show SChain [up i,up j,up a] (crossL [] i j [up a]) [up j,up i,up a] from ⟨rfl,rfl⟩)
    (show SChain [up j,up i,up a] (crossL [up j] i a []) [up j,up a,up i] from ⟨rfl,rfl⟩)
    (show SChain [up j,up a,up i] (crossL [] j a [up i]) [up a,up j,up i] from ⟨rfl,rfl⟩)).trans
    (congrArg₂ (· ≫ ·) (eval_cross_left3 t ν μ i j a h _)
      (congrArg₂ (· ≫ ·) (eval_cross_right3 t ν μ j i a _ _) (eval_cross_left3 t ν μ j a i _ h')))

theorem eval_braid_right (t : k) (ν μ : X) (i j a : I) (h : wt D μ [up i,up j,up a] = ν)
    (h' : wt D μ [up a,up j,up i] = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ
      (crossL [up i] j a [] ++ crossL [] i a [up j] ++ crossL [up a] i j []) h h'
      (by simp [crossL, Shape.dom, Shape.cod]) =
      crossRight3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h ≫
        crossLeft3 t ν μ i a j ((wt_swap_right3 μ i j a).trans h) ≫
        crossRight3 t ν μ a i j ((wt_swap_left3 μ i a j).trans ((wt_swap_right3 μ i j a).trans h)) := by
  exact (eval_append3 t ν μ _ _ _ h ((wt_swap_right3 μ i j a).trans h)
    ((wt_swap_left3 μ i a j).trans ((wt_swap_right3 μ i j a).trans h)) h'
    (show SChain [up i,up j,up a] (crossL [up i] j a []) [up i,up a,up j] from ⟨rfl,rfl⟩)
    (show SChain [up i,up a,up j] (crossL [] i a [up j]) [up a,up i,up j] from ⟨rfl,rfl⟩)
    (show SChain [up a,up i,up j] (crossL [up a] i j []) [up a,up j,up i] from ⟨rfl,rfl⟩)).trans
    (congrArg₂ (· ≫ ·) (eval_cross_right3 t ν μ i j a h _)
      (congrArg₂ (· ≫ ·) (eval_cross_left3 t ν μ i a j _ _) (eval_cross_right3 t ν μ a i j _ h')))

theorem rhoLin_braid (t : k) (μ : X) (i j a : I) (hia : ¬(i = a ∧ i ≠ j)) :
    rhoLin (sy := sy) (hc := hc) t (wt D μ [up i,up j,up a]) μ rfl
      (by simp [wt, sh, add_comm, add_left_comm, add_assoc])
      (relation D Sc (.braid i j a μ hia)) = 0 := by
  apply forget_injective (wt D μ [up i,up j,up a]) μ rfl
    (show wt D μ [up a,up j,up i] = wt D μ [up i,up j,up a] by simp [wt, sh, add_comm, add_left_comm, add_assoc])
  simp only [map_zero]
  change evalLin (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up i,up j,up a]) μ rfl _
    (relation D Sc (.braid i j a μ hia)) = 0
  simp only [relation, map_sub, evalLin_dg, eval_braid_left, eval_braid_right]
  exact sub_eq_zero.mpr (crossing_braid_ne (Sc := Sc) (sy := sy) (hc := hc) t _ μ i j a rfl hia)

end OddMath.SKM.RhoUpwardKernel
