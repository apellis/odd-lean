import OddMath.Frontier.NilHeckeRightKernel

/-!
# Entire commutant of the actual natural action
EKL arXiv:1111.1320v1 (2.1), (2.3)-(2.4), §2.2 natural action.
Corollary 2.14 motivates, but is not a premise or a conclusion here.
No faithfulness, nilHecke PBW, or double-centralizer claim.
-/
namespace OddMath.Frontier.NilHeckeCommutant
open OddMath.SkewPolynomial (SkewPolynomial generator)
open NilHeckeAction NilHeckeRightKernel OddSymmetricKernel

/-- Literal ordinary commutation with every element of the actual quotient action. -/
noncomputable def actionCommutant (n : ℕ) : Subring (Module.End ℤ (SkewPolynomial (n+2))) where
  carrier := {F | ∀ a : NilHeckeAction.Presented n, action n a * F = F * action n a}
  zero_mem' := by intro a; simp
  one_mem' := by intro a; simp
  add_mem' := by
    intro F G hF hG a
    rw [mul_add, add_mul, hF a, hG a]
  neg_mem' := by
    intro F hF a
    rw [mul_neg, neg_mul, hF a]
  mul_mem' := by
    intro F G hF hG a
    rw [← mul_assoc, hF a, mul_assoc, hG a, ← mul_assoc]

@[simp] theorem mem_actionCommutant (n : ℕ) (F : Module.End ℤ (SkewPolynomial (n+2))) :
    F ∈ actionCommutant n ↔ ∀ a : NilHeckeAction.Presented n,
      action n a * F = F * action n a := Iff.rfl

/-- Dot commutation forces left linearity by genuine free-algebra generation.
The generator hypothesis is not replaced by assumed left linearity. -/
theorem map_mul_of_commutes_dots (n : ℕ) (F : Module.End ℤ (SkewPolynomial (n+2)))
    (h : ∀ j : Fin (n+2), action n (dot n j) * F = F * action n (dot n j))
    (a f : SkewPolynomial (n+2)) : F (a*f) = a * F f := by
  have hj (j : Fin (n+2)) (b : SkewPolynomial (n+2)) :
      F (generator j * b) = generator j * F b := by
    have he := congrArg (fun T : Module.End ℤ (SkewPolynomial (n+2)) => T b) (h j)
    simpa only [end_mul_apply, action_dot_apply] using he.symm
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective (n+2) a
  induction x using Quotient.inductionOn' with
  | h w =>
      change F (PbwL3.evalAlg (n+2) w * f) = PbwL3.evalAlg (n+2) w * F f
      induction w using FreeAlgebra.induction generalizing f with
      | grade0 z =>
          rw [AlgHom.commutes]
          change F ((z • 1) * f) = (z • 1) * F f
          simp only [smul_mul_assoc, one_mul, map_smul]
      | grade1 j =>
          rw [PbwL3.evalAlg_ι]
          exact hj j f
      | add u v ihu ihv =>
          rw [map_add, add_mul, map_add, ihu, ihv, add_mul]
      | mul u v ihu ihv =>
          rw [map_mul (PbwL3.evalAlg (n+2)) u v, mul_assoc, ihu, ihv, mul_assoc]

/-- An arbitrary integer-linear endomorphism commuting with dots is R_(F 1). -/
theorem end_eq_rightOperator_of_commutes_dots (n : ℕ)
    (F : Module.End ℤ (SkewPolynomial (n+2)))
    (h : ∀ j : Fin (n+2), action n (dot n j) * F = F * action n (dot n j)) :
    F = rightOperator n (F 1) := by
  apply LinearMap.ext
  intro f
  simpa only [mul_one, rightOperator_apply] using map_mul_of_commutes_dots n F h f 1

@[simp] theorem rightOperator_one (n : ℕ) (g : SkewPolynomial (n+2)) :
    rightOperator n g 1 = g := by rw [rightOperator_apply, one_mul]

/-- Evaluation at one is injective on genuine right multiplication maps. -/
theorem rightOperator_injective (n : ℕ) : Function.Injective (rightOperator n) := by
  intro g h he
  simpa only [rightOperator_one] using
    congrArg (fun T : Module.End ℤ (SkewPolynomial (n+2)) => T 1) he

/-- Dot rigidity plus the parent's crossing-at-one converse identifies the factor. -/
theorem eval_one_mem_kernel (n : ℕ) (F : Module.End ℤ (SkewPolynomial (n+2)))
    (hF : F ∈ actionCommutant n) : F 1 ∈ kernelSubring n := by
  have he := end_eq_rightOperator_of_commutes_dots n F (fun j => hF (dot n j))
  apply (mem_kernel_iff_commutes_right n (F 1)).mpr
  intro a
  rw [← he]
  exact hF a

/-- The entire End_Z commutant, not just a predicate on preselected right maps. -/
theorem mem_actionCommutant_iff (n : ℕ) (F : Module.End ℤ (SkewPolynomial (n+2))) :
    F ∈ actionCommutant n ↔ ∃ g : kernelSubring n,
      F = rightOperator n (g : SkewPolynomial (n+2)) := by
  constructor
  · intro hF
    exact ⟨⟨F 1, eval_one_mem_kernel n F hF⟩,
      end_eq_rightOperator_of_commutes_dots n F (fun j => hF (dot n j))⟩
  · rintro ⟨g, rfl⟩ a
    exact action_commutes_right n a g g.property

/-- Every commuting endomorphism has exactly one actual kernel right factor. -/
theorem unique_right_factor (n : ℕ) (F : Module.End ℤ (SkewPolynomial (n+2)))
    (hF : F ∈ actionCommutant n) : ∃! g : kernelSubring n,
      F = rightOperator n (g : SkewPolynomial (n+2)) := by
  obtain ⟨g, hg⟩ := (mem_actionCommutant_iff n F).mp hF
  refine ⟨g, hg, ?_⟩
  intro h hh
  apply Subtype.ext
  exact rightOperator_injective n (hh.symm.trans hg)

/-- Any right-factor witness is recovered by evaluation at one. -/
theorem eval_one_eq_factor (n : ℕ) (F : Module.End ℤ (SkewPolynomial (n+2)))
    (g : kernelSubring n) (h : F = rightOperator n (g : SkewPolynomial (n+2))) :
    F 1 = (g : SkewPolynomial (n+2)) := by rw [h, rightOperator_one]

/-- For arbitrary factors, composition reverses their order. -/
theorem rightOperator_mul (n : ℕ) (g h : SkewPolynomial (n+2)) :
    rightOperator n g * rightOperator n h = rightOperator n (h*g) := by
  apply LinearMap.ext
  intro f
  exact mul_assoc f h g

/-- Pointwise arbitrary-input consumer of rigidity. -/
theorem commutant_apply (n : ℕ) (F : Module.End ℤ (SkewPolynomial (n+2)))
    (hF : F ∈ actionCommutant n) (f : SkewPolynomial (n+2)) : F f = f * F 1 := by
  have he := end_eq_rightOperator_of_commutes_dots n F (fun j => hF (dot n j))
  exact congrArg (fun T : Module.End ℤ (SkewPolynomial (n+2)) => T f) he

/-- Actual closure with its right factor, in reversed order, identified. -/
theorem kernel_right_composition (n : ℕ) (g h : kernelSubring n) :
    rightOperator n (g : SkewPolynomial (n+2)) * rightOperator n (h : SkewPolynomial (n+2))
        ∈ actionCommutant n ∧
      rightOperator n (g : SkewPolynomial (n+2)) * rightOperator n (h : SkewPolynomial (n+2)) =
        rightOperator n ((h*g : kernelSubring n) : SkewPolynomial (n+2)) := by
  have he := rightOperator_mul n (g : SkewPolynomial (n+2)) (h : SkewPolynomial (n+2))
  refine ⟨?_, he⟩
  rw [he]
  exact (mem_actionCommutant_iff n _).mpr ⟨h*g, rfl⟩

/-- Closure and factor evaluation for arbitrary commuting endomorphisms. -/
theorem commutant_composition (n : ℕ) (F G : Module.End ℤ (SkewPolynomial (n+2)))
    (hF : F ∈ actionCommutant n) (hG : G ∈ actionCommutant n) :
    F*G ∈ actionCommutant n ∧ F*G = rightOperator n (G 1 * F 1) ∧
      (F*G) 1 = G 1 * F 1 := by
  refine ⟨(actionCommutant n).mul_mem hF hG, ?_, ?_⟩
  · conv_lhs =>
      rw [end_eq_rightOperator_of_commutes_dots n F (fun j => hF (dot n j)),
        end_eq_rightOperator_of_commutes_dots n G (fun j => hG (dot n j))]
    exact rightOperator_mul n (F 1) (G 1)
  · exact commutant_apply n F hF (G 1)

/-- Tiny positive diagnostic, inherited from the actual divided kernel. -/
theorem rankTwo_difference_commutes :
    rightOperator 0 (generator (0 : Fin 2) - generator 1) ∈ actionCommutant 0 :=
  (mem_actionCommutant_iff 0 _).mpr ⟨⟨_, rankTwo_difference_mem⟩, rfl⟩

/-- Tiny negative diagnostic; no exterior-algebra replacement. -/
theorem rankTwo_generator_not_mem :
    rightOperator 0 (generator (0 : Fin 2)) ∉ actionCommutant 0 := by
  intro h
  exact rankTwo_generator_not_commutes (h (crossing 0 0))

end OddMath.Frontier.NilHeckeCommutant
