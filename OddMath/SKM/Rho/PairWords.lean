import OddMath.SKM.Rho.WordComparison

/-!
# Pair Words for ρ

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

theorem eval_pair_append (t : k) (ν μ : X) (L M : List (LayerData I))
    (i j a b c d : I) (hs : wt D μ [up i,up j] = ν)
    (hr : wt D μ [up a,up b] = ν) (hq : wt D μ [up c,up d] = ν)
    (hL : SChain [up i,up j] L [up a,up b]) (hM : SChain [up a,up b] M [up c,up d]) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (L ++ M) hs hq (hL.append hM) =
      eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ L hs hr hL ≫
      eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ M hr hq hM :=
  eval_append t ν μ L M hs hr hq hL hM

theorem eval_lx (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j] = ν)
    (h' : wt D μ [up j,up i] = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ
      (dotsL [] i [up j] 1 ++ crossL [] i j []) h h'
      (by simp [dotsL, crossL, Shape.dom, Shape.cod]) =
    (show (pres D Sc).obj (ob D ν [dn j,dn i]) ⟶ (pres D Sc).obj (ob D ν [dn j,dn i]) from
      rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) ≫
      correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h := by
  calc
    _ = eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (dotsL [] i [up j] 1) h h (sChain_dotsL [] i [up j] 1) ≫
        eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (crossL [] i j []) h h'
          (by simp [crossL, Shape.dom, Shape.cod]) := eval_append t ν μ _ _ h h h' _ _
    _ = _ := by
      simp only [dotsL, List.replicate_one]
      erw [eval_dot_left, eval_cross]

theorem eval_xr (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j] = ν)
    (h' : wt D μ [up j,up i] = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (crossL [] i j [] ++ dotsL [up j] i [] 1) h h'
      (by simp [dotsL, crossL, Shape.dom, Shape.cod]) =
    (show (pres D Sc).obj (ob D ν [dn j,dn i]) ⟶ (pres D Sc).obj (ob D ν [dn i,dn j]) from
      correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) ≫ rhoDotRight (Sc := Sc) (sy := sy) (hc := hc) t ν μ j i h' := by
  calc
    _ = eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (crossL [] i j []) h h' (by simp [crossL, Shape.dom, Shape.cod]) ≫
        eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (dotsL [up j] i [] 1) h' h' (by simp [dotsL, Shape.dom, Shape.cod]) :=
      eval_append t ν μ _ _ h h' h' _ _
    _ = _ := by
      simp only [dotsL, List.replicate_one]
      erw [eval_cross, eval_dot_right]

theorem eval_xl (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j] = ν)
    (h' : wt D μ [up j,up i] = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (crossL [] i j [] ++ dotsL [] j [up i] 1) h h'
      (by simp [dotsL, crossL, Shape.dom, Shape.cod]) =
    (show (pres D Sc).obj (ob D ν [dn j,dn i]) ⟶ (pres D Sc).obj (ob D ν [dn i,dn j]) from
      correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) ≫ rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ j i h' := by
  calc
    _ = eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (crossL [] i j []) h h' (by simp [crossL, Shape.dom, Shape.cod]) ≫
        eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (dotsL [] j [up i] 1) h' h' (by simp [dotsL, Shape.dom, Shape.cod]) :=
      eval_append t ν μ _ _ h h' h' _ _
    _ = _ := by
      simp only [dotsL, List.replicate_one]
      erw [eval_cross, eval_dot_left]

theorem eval_rx (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j] = ν)
    (h' : wt D μ [up j,up i] = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (dotsL [up i] j [] 1 ++ crossL [] i j []) h h'
      (by simp [dotsL, crossL, Shape.dom, Shape.cod]) =
    (show (pres D Sc).obj (ob D ν [dn j,dn i]) ⟶ (pres D Sc).obj (ob D ν [dn j,dn i]) from
      rhoDotRight (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) ≫ correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h := by
  calc
    _ = eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (dotsL [up i] j [] 1) h h (by simp [dotsL, Shape.dom, Shape.cod]) ≫
        eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (crossL [] i j []) h h' (by simp [crossL, Shape.dom, Shape.cod]) :=
      eval_append t ν μ _ _ h h h' _ _
    _ = _ := by
      simp only [dotsL, List.replicate_one]
      erw [eval_dot_right, eval_cross]

end OddMath.SKM.RhoUpwardKernel
