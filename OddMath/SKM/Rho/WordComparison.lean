import OddMath.SKM.Rho.SmallLayers

/-!
# Word Comparison for ρ

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

def eval (t : k) (ν μ : X) (L : List (LayerData I)) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (h : SChain s L r) :=
  forget (Sc := Sc) (sy := sy) (hc := hc) ν μ hs hr (rhoRaw t ν μ L hs hr h)

theorem eval_append (t : k) (ν μ : X) (L M : List (LayerData I)) {s r q : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (hq : wt D μ q = ν)
    (hL : SChain s L r) (hM : SChain r M q) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (L ++ M) hs hq (hL.append hM) =
      eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ L hs hr hL ≫ eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ M hr hq hM := by
  unfold eval
  erw [rhoRaw_append t ν μ L M hs hr hq hL hM, forget_comp ν μ hs hr hq]

theorem eval_nil (t : k) (ν μ : X) (s : List (Letter I)) (h : wt D μ s = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ [] h h rfl = 𝟙 _ := by
  exact forget_id ν μ s h

theorem eval_dots (t : k) (ν μ : X) (u v : List (Letter I)) (i : I)
    (h : wt D μ (u ++ [up i] ++ v) = ν) (n : ℕ) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (dotsL u i v n) h h (sChain_dotsL u i v n) =
      cpow (eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ [(u, .dot i, v)] h h ⟨rfl,rfl⟩) n := by
  induction n with
  | zero => exact eval_nil t ν μ _ h
  | succ n ih =>
    have he : dotsL u i v (n+1) = dotsL u i v n ++ [(u, .dot i, v)] := by
      simp [dotsL, List.replicate_succ']
    simp only [he]
    erw [eval_append t ν μ (dotsL u i v n) [(u, .dot i, v)] h h h (sChain_dotsL u i v n) ⟨rfl,rfl⟩]
    rw [ih, cpow_succ]

theorem eval_dot_left (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j] = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ [([], .dot i, [up j])] h h ⟨rfl,rfl⟩ =
      rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h := dot_left t ν μ i j h

theorem eval_dot_right (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j] = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ [([up i], .dot j, [])] h h ⟨rfl,rfl⟩ =
      rhoDotRight (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h := dot_right t ν μ i j h

theorem eval_cross (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j] = ν)
    (h' : wt D μ [up j,up i] = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (crossL [] i j []) h h'
      (by simp [crossL, Shape.dom, Shape.cod]) =
      correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h := by
  exact (bare_cross t ν μ i j h).trans (correctedCrossing_eq t ν μ i j h).symm

theorem forget_dg (t : k) (ν μ : X) (L : List (LayerData I)) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (h : SChain s L r) :
    forget (Sc := Sc) (sy := sy) (hc := hc) ν μ hs hr (rhoLin t ν μ hs hr (dg D μ L h)) =
      eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ L hs hr h := by
  erw [rhoLin_dg]
  rfl

theorem forget_idg (t : k) (ν μ : X) (s : List (Letter I)) (h : wt D μ s = ν) :
    forget (Sc := Sc) (sy := sy) (hc := hc) ν μ h h (rhoLin t ν μ h h (idg D μ s)) = 𝟙 _ := by
  erw [rhoLin_idg, forget_id]

end OddMath.SKM.RhoUpwardKernel
