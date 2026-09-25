import OddMath.Frontier.DividedSquareZero

namespace OddMath.Frontier.DividedBraid
open PbwL2 PbwL3 AllRankDivided DividedSquareZero
open OddMath.SkewPolynomial (SkewPolynomial generator)
variable {n : ℕ}

/-- Left multiplication by every generator preserves braid equality at an
arbitrary right input. All three active positions and every spectator occur. -/
private theorem braid_generator (i : Fin (n+1)) (j : Fin (n+3))
    (f : SkewPolynomial (n+3))
    (h : divided i.castSucc (divided i.succ (divided i.castSucc f)) =
      divided i.succ (divided i.castSucc (divided i.succ f))) :
    divided i.castSucc (divided i.succ (divided i.castSucc (generator j * f))) =
      divided i.succ (divided i.castSucc (divided i.succ (generator j * f))) := by
  have h01 : i.castSucc.castSucc ≠ i.succ.castSucc := by
    intro e
    have e' := congrArg Fin.val e
    simp only [Fin.coe_castSucc, Fin.val_succ] at e'
    omega
  have h02 : i.castSucc.castSucc ≠ i.succ.succ := by
    intro e
    have e' := congrArg Fin.val e
    simp only [Fin.coe_castSucc, Fin.val_succ] at e'
    omega
  have h20 : i.succ.succ ≠ i.castSucc.castSucc := Ne.symm h02
  have h21 : i.succ.succ ≠ i.castSucc.succ := by
    intro e
    have e' := congrArg Fin.val e
    simp only [Fin.coe_castSucc, Fin.val_succ] at e'
    omega
  have haL (g : SkewPolynomial (n+3)) := divided_left_mul i.castSucc g
  have haM (g : SkewPolynomial (n+3)) := divided_right_mul i.castSucc g
  have haR (g : SkewPolynomial (n+3)) := divided_spectator_mul i.castSucc _ h20 h21 g
  have hbL (g : SkewPolynomial (n+3)) := divided_spectator_mul i.succ _ h01 h02 g
  have hbM (g : SkewPolynomial (n+3)) :
      divided i.succ (generator i.castSucc.succ * g) =
        g - generator i.succ.succ * divided i.succ g := divided_left_mul i.succ g
  have hbR (g : SkewPolynomial (n+3)) :
      divided i.succ (generator i.succ.succ * g) =
        g - generator i.castSucc.succ * divided i.succ g := divided_right_mul i.succ g
  by_cases hl : j = i.castSucc.castSucc
  · subst j
    simp only [haL, haM, haR, hbL, hbM, hbR,
      neg_mul, map_neg, map_sub, divided_sq_zero, map_zero]
    rw [h]
    abel
  · by_cases hm : j = i.castSucc.succ
    · subst j
      simp only [haL, haM, haR, hbL, hbM, hbR,
        neg_mul, map_neg, map_sub, divided_sq_zero, map_zero]
      rw [h]
      abel
    · by_cases hr : j = i.succ.succ
      · subst j
        simp only [haL, haM, haR, hbL, hbM, hbR,
          neg_mul, map_neg, map_sub, divided_sq_zero, map_zero]
        rw [h]
        abel
      · simp only [divided_spectator_mul i.castSucc j hl hm,
          divided_spectator_mul i.succ j hm hr, neg_mul, map_neg]
        rw [h]

/-- Genuine generation induction, not a reduction to active variables.
The right-input-parametric formulation makes the product step non-circular. -/
private theorem braid_mul (i : Fin (n+1)) (a f : SkewPolynomial (n+3))
    (h : divided i.castSucc (divided i.succ (divided i.castSucc f)) =
      divided i.succ (divided i.castSucc (divided i.succ f))) :
    divided i.castSucc (divided i.succ (divided i.castSucc (a * f))) =
      divided i.succ (divided i.castSucc (divided i.succ (a * f))) := by
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective (n+3) a
  induction x using Quotient.inductionOn' with
  | h w =>
      change divided i.castSucc (divided i.succ (divided i.castSucc (evalAlg (n+3) w * f))) =
        divided i.succ (divided i.castSucc (divided i.succ (evalAlg (n+3) w * f)))
      induction w using FreeAlgebra.induction generalizing f with
      | grade0 r =>
          rw [AlgHom.commutes]
          change divided i.castSucc (divided i.succ (divided i.castSucc ((r • 1) * f))) =
            divided i.succ (divided i.castSucc (divided i.succ ((r • 1) * f)))
          simp only [smul_mul_assoc, one_mul, map_smul, h]
      | grade1 j =>
          rw [evalAlg_ι]
          exact braid_generator i j f h
      | add a b ha hb =>
          rw [map_add, add_mul, map_add, map_add, map_add, map_add, map_add, map_add,
            ha f h, hb f h]
      | mul a b ha hb =>
          rw [map_mul (evalAlg (n+3)) a b, mul_assoc]
          exact ha _ (hb f h)

/-- The positive adjacent braid relation for the actual integral operators. -/
theorem divided_braid (i : Fin (n+1)) (f : SkewPolynomial (n+3)) :
    divided i.castSucc (divided i.succ (divided i.castSucc f)) =
      divided i.succ (divided i.castSucc (divided i.succ f)) := by
  have h : divided i.castSucc (divided i.succ (divided i.castSucc 1)) =
      divided i.succ (divided i.castSucc (divided i.succ 1)) := by
    simp only [divided_one, map_zero]
  simpa only [mul_one] using braid_mul i f 1 h

/-- Exact equality of the genuine linear-map compositions. -/
theorem divided_braid_comp (i : Fin (n+1)) :
    (divided i.castSucc).comp ((divided i.succ).comp (divided i.castSucc)) =
      (divided i.succ).comp ((divided i.castSucc).comp (divided i.succ)) := by
  apply LinearMap.ext
  intro f
  exact divided_braid i f

/-- The common triple image lies in both adjacent kernels. -/
theorem divided_triple_image (i : Fin (n+1)) (f : SkewPolynomial (n+3)) :
    divided i.castSucc (divided i.castSucc (divided i.succ (divided i.castSucc f))) = 0 ∧
      divided i.succ (divided i.castSucc (divided i.succ (divided i.castSucc f))) = 0 := by
  constructor
  · exact divided_sq_zero _ _
  · rw [divided_braid i f]
    exact divided_sq_zero _ _

end OddMath.Frontier.DividedBraid
