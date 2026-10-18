import OddMath.SKM.Rho.BraidKernel
import OddMath.SKM.Rho.ShiftedBraid

/-!
# Triple Powers for ρ

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

theorem dot_last3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ [up i,up j,up a] = ν) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ [([up i,up j], .dot a, [])] h h ⟨rfl,rfl⟩ =
      dotLast3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h := by
  subst ν
  have H := eval_whisk_left (Sc := Sc) (sy := sy) (hc := hc) t
    (wt D μ [up i,up j,up a]) (wt D μ [up j,up a]) μ [i] [j,a] [j,a]
    [([up j], .dot a, [])] rfl rfl rfl ⟨rfl,rfl⟩
  have E : upEval (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up j,up a]) μ
      [([up j], .dot a, [])] (s := [j,a]) (r := [j,a]) rfl rfl ⟨rfl,rfl⟩ =
      rhoDotRight (Sc := Sc) (sy := sy) (hc := hc) t (wt D μ [up j,up a]) μ j a rfl :=
    eq_of_heq ((upEval_heq_eval t _ μ _ rfl rfl _).trans (heq_of_eq (eval_dot_right t _ μ j a rfl)))
  rw [E] at H
  exact eq_of_heq (H.trans (dotLast3_whisker t μ i j a))

theorem eval_dots_first3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ [up i,up j,up a] = ν) (n : ℕ) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (dotsL [] i [up j,up a] n) h h (sChain_dotsL [] i [up j,up a] n) =
      cpow (dotFirst3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h) n := by
  erw [eval_dots]
  change cpow (forget ν μ h h (rhoRaw t ν μ _ h h _)) n = _
  erw [dot_first3]
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun f : (pres D Sc).obj (ob D ν [dn a,dn j,dn i]) ⟶ (pres D Sc).obj (ob D ν [dn a,dn j,dn i]) => f ≫
      (QEnvelope.toHom (Envelope.toHom (dotFirst3 (sy := sy) (hc := hc) t ν μ i j a h)))) ih

theorem eval_dots_middle3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ [up i,up j,up a] = ν) (n : ℕ) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (dotsL [up i] j [up a] n) h h (sChain_dotsL [up i] j [up a] n) =
      cpow (dotMiddle3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h) n := by
  erw [eval_dots, dot_middle3]
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun f : (pres D Sc).obj (ob D ν [dn a,dn j,dn i]) ⟶ (pres D Sc).obj (ob D ν [dn a,dn j,dn i]) => f ≫
      (QEnvelope.toHom (Envelope.toHom (dotMiddle3 (sy := sy) (hc := hc) t ν μ i j a h)))) ih

theorem eval_dots_last3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ [up i,up j,up a] = ν) (n : ℕ) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ (dotsL [up i,up j] a [] n) h h (sChain_dotsL [up i,up j] a [] n) =
      cpow (dotLast3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h) n := by
  erw [eval_dots, dot_last3]
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun f : (pres D Sc).obj (ob D ν [dn a,dn j,dn i]) ⟶ (pres D Sc).obj (ob D ν [dn a,dn j,dn i]) => f ≫
      (QEnvelope.toHom (Envelope.toHom (dotLast3 (sy := sy) (hc := hc) t ν μ i j a h)))) ih

theorem eval_braid_monomial (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j,up i] = ν) (r q s : ℕ) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ
      (dotsL [up i,up j] i [] s ++ dotsL [up i] j [up i] q ++ dotsL [] i [up j,up i] r)
      h h (((sChain_dotsL [up i,up j] i [] s).append (sChain_dotsL [up i] j [up i] q)).append
        (sChain_dotsL [] i [up j,up i] r)) = braidMonomial (Sc := Sc) t ν i j r q s := by
  calc
    _ = rhoForget3 (Sc := Sc) (sy := sy) (hc := hc) ν μ i j i h
        (cpow (dotLast3 t ν μ i j i h) s ≫ cpow (dotMiddle3 t ν μ i j i h) q ≫
          cpow (dotFirst3 t ν μ i j i h) r) :=
      (eval_append3 t ν μ _ _ _ h h h h _ _ _).trans
        (congrArg₂ (· ≫ ·) (eval_dots_last3 t ν μ i j i h s)
          (congrArg₂ (· ≫ ·) (eval_dots_middle3 t ν μ i j i h q) (eval_dots_first3 t ν μ i j i h r)))
    _ = _ := braidMonomial_powers t ν μ i j h r q s

theorem eval_braid_monomial_zero (t : k) (ν μ : X) (i j : I) (h : wt D μ [up i,up j,up i] = ν) (r s : ℕ) :
    eval (Sc := Sc) (sy := sy) (hc := hc) t ν μ
      (dotsL [up i,up j] i [] s ++ dotsL [] i [up j,up i] r)
      h h ((sChain_dotsL [up i,up j] i [] s).append (sChain_dotsL [] i [up j,up i] r)) =
      braidMonomial (Sc := Sc) t ν i j r 0 s := by
  simpa only [dotsL, List.replicate_zero, List.append_nil] using eval_braid_monomial t ν μ i j h r 0 s

end OddMath.SKM.RhoUpwardKernel
