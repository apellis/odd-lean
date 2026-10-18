import OddMath.SKM.Rho.PairWords

/-!
# Pair Powers for ρ

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

theorem eval_dots_left (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j] = ν) (n : ℕ) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (dotsL [] i [up j] n) h h (sChain_dotsL [] i [up j] n) =
      cpow (rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) n := by
  erw [eval_dots, eval_dot_left]
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun f => f ≫
      (show (pres D Sc).obj (ob D ν [dn j,dn i]) ⟶ _ from rhoDotLeft (sy := sy) (hc := hc) t ν μ i j h)) ih

theorem eval_dots_right (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j] = ν) (n : ℕ) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (dotsL [up i] j [] n) h h (sChain_dotsL [up i] j [] n) =
      cpow (rhoDotRight (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) n := by
  erw [eval_dots, eval_dot_right]
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun f => f ≫
      (show (pres D Sc).obj (ob D ν [dn j,dn i]) ⟶ _ from rhoDotRight (sy := sy) (hc := hc) t ν μ i j h)) ih

theorem eval_pair_monomial (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j] = ν) (p q : ℕ) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (dotsL [up i] j [] q ++ dotsL [] i [up j] p)
      h h ((sChain_dotsL [up i] j [] q).append (sChain_dotsL [] i [up j] p)) =
      QEnvelope.toHom (Envelope.toHom (cpow (rhoDotRight (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) q)) ≫
        QEnvelope.toHom (Envelope.toHom (cpow (rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) p)) := by
  exact (eval_append t ν μ _ _ h h h _ _).trans
    (congrArg₂ (· ≫ ·) (eval_dots_right t ν μ i j h q) (eval_dots_left t ν μ i j h p))

theorem eval_xx (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j] = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (crossL [] i j [] ++ crossL [] j i []) h h
      (by simp [crossL, Shape.dom, Shape.cod]) =
      (show (pres D Sc).obj (ob D ν [dn j,dn i]) ⟶ _ from
        correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) ≫
        correctedCrossing (Sc := Sc) (sy := sy) (hc := hc) t ν μ j i
          (by simpa [ups, wt, sh, add_comm, add_left_comm, add_assoc] using h) := by
  have hj : wt D μ [up j,up i] = ν := by simpa [wt, sh, add_comm, add_left_comm, add_assoc] using h
  exact (eval_append t ν μ _ _ h hj h
    (show SChain [up i,up j] (crossL [] i j []) [up j,up i] by simp [crossL, Shape.dom, Shape.cod])
    (show SChain [up j,up i] (crossL [] j i []) [up i,up j] by simp [crossL, Shape.dom, Shape.cod])).trans
    (congrArg₂ (· ≫ ·) (eval_cross t ν μ i j h hj) (eval_cross t ν μ j i hj h))

end OddMath.SKM.RhoUpwardKernel
