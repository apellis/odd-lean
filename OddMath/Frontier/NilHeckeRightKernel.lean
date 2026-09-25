import OddMath.Frontier.NilHeckeAction
import OddMath.Frontier.OddSymmetricKernel

/-! Right joint-kernel linearity of the actual presented nilHecke action.
EKL 1111.1320v1 (2.4), §2.2. No faithfulness or full commutant claim. -/
namespace OddMath.Frontier.NilHeckeRightKernel
open OddMath.SkewPolynomial (SkewPolynomial generator)
open NilHeckeAction OddSymmetricKernel AllRankDivided

noncomputable def rightOperator (n : ℕ) (g : SkewPolynomial (n+2)) :
    Module.End ℤ (SkewPolynomial (n+2)) := LinearMap.mulRight ℤ g

@[simp] theorem rightOperator_apply (n : ℕ) (g f : SkewPolynomial (n+2)) :
    rightOperator n g f = f*g := rfl

/-- Only the right factor is in the actual joint kernel. No signed invariance is used. -/
theorem divided_right_kernel (n : ℕ) (i : Fin (n+1))
    (g : SkewPolynomial (n+2)) (hg : g ∈ kernelSubring n)
    (f : SkewPolynomial (n+2)) : divided i (f*g) = divided i f*g := by
  rw [divided_mul, (mem_kernelSubring g).mp hg i, mul_zero, add_zero]

/-- All free expressions, including scalar combinations and repeated dot powers. -/
theorem freeAction_right_mul (n : ℕ) (w : Free n)
    (g : SkewPolynomial (n+2)) (hg : g ∈ kernelSubring n)
    (f : SkewPolynomial (n+2)) : freeAction n w (f*g) = freeAction n w f*g := by
  induction w using FreeAlgebra.induction generalizing f with
  | grade0 z =>
      rw [AlgHom.commutes]
      change z • (f*g) = (z • f)*g
      exact (smul_mul_assoc z f g).symm
  | grade1 j =>
      cases j with
      | inl j =>
          change freeAction n (dotFree n j) (f*g) = freeAction n (dotFree n j) f*g
          rw [freeAction_dot]
          change generator j * (f*g) = (generator j * f)*g
          exact (mul_assoc _ _ _).symm
      | inr i =>
          change freeAction n (crossingFree n i) (f*g) = freeAction n (crossingFree n i) f*g
          rw [freeAction_crossing]
          change divided i (f*g) = divided i f*g
          exact divided_right_kernel n i g hg f
  | mul u v ihu ihv =>
      simp only [map_mul, end_mul_apply]
      rw [ihv, ihu]
  | add u v ihu ihv =>
      simp only [map_add, LinearMap.add_apply, ihu, ihv, add_mul]

/-- Descend along the literal quotient map, not an assumed faithful representation. -/
theorem action_right_mul (n : ℕ) (a : NilHeckeAction.Presented n)
    (g : SkewPolynomial (n+2)) (hg : g ∈ kernelSubring n)
    (f : SkewPolynomial (n+2)) : action n a (f*g) = action n a f*g := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact freeAction_right_mul n w g hg f

/-- End multiplication composes with the left factor acting last. -/
theorem action_commutes_right (n : ℕ) (a : NilHeckeAction.Presented n)
    (g : SkewPolynomial (n+2)) (hg : g ∈ kernelSubring n) :
    action n a * rightOperator n g = rightOperator n g * action n a := by
  apply LinearMap.ext
  intro f
  exact action_right_mul n a g hg f

/-- Characterizes commuting RIGHT multiplications only, not the entire commutant. -/
theorem mem_kernel_iff_commutes_right (n : ℕ) (g : SkewPolynomial (n+2)) :
    g ∈ kernelSubring n ↔ ∀ a : NilHeckeAction.Presented n,
      action n a * rightOperator n g = rightOperator n g * action n a := by
  constructor
  · intro hg a
    exact action_commutes_right n a g hg
  · intro h
    rw [mem_kernelSubring]
    intro i
    have he := congrArg (fun T : Module.End ℤ (SkewPolynomial (n+2)) => T 1)
      (h (crossing n i))
    rw [action_crossing] at he
    change divided i (1*g) = divided i 1*g at he
    simpa only [one_mul, divided_one, zero_mul] using he

/-- Direct subtype consumer; the factor order is intentionally explicit. -/
theorem action_right_mul_kernel (n : ℕ) (a : NilHeckeAction.Presented n)
    (g : kernelSubring n) (f : SkewPolynomial (n+2)) :
    action n a (f * (g : SkewPolynomial (n+2))) =
      action n a f * (g : SkewPolynomial (n+2)) :=
  action_right_mul n a g.val g.property f

/-- Use the inherited literal elementary sums and their proved membership. -/
theorem action_right_mul_elementary (n k : ℕ) (a : NilHeckeAction.Presented n)
    (f : SkewPolynomial (n+2)) :
    action n a (f * FiniteCompleteElementary.elementaryPoly (n+2) k) =
      action n a f * FiniteCompleteElementary.elementaryPoly (n+2) k :=
  action_right_mul n a _ (elementary_mem n k) f

/-- Complete sums retain arbitrary repeated letters and arbitrary degree. -/
theorem action_right_mul_complete (n k : ℕ) (a : NilHeckeAction.Presented n)
    (f : SkewPolynomial (n+2)) :
    action n a (f * FiniteCompleteElementary.completePoly (n+2) k) =
      action n a f * FiniteCompleteElementary.completePoly (n+2) k :=
  action_right_mul n a _ (complete_mem n k) f

/-- Hand boundary: D₀(x₀-x₁)=1-1=0. -/
theorem rankTwo_difference_mem :
    (generator (0 : Fin 2) - generator (1 : Fin 2)) ∈ kernelSubring 0 := by
  rw [mem_kernelSubring]
  intro i
  have hi : i = 0 := Fin.ext (by have h := i.isLt; omega)
  subst i
  simp [map_sub, divided_generator]

/-- The tiny positive boundary still has arbitrary action and polynomial input. -/
theorem rankTwo_difference_right_mul (a : NilHeckeAction.Presented 0)
    (f : SkewPolynomial 2) :
    action 0 a (f * (generator 0 - generator 1)) =
      action 0 a f * (generator 0 - generator 1) :=
  action_right_mul 0 a _ rankTwo_difference_mem f

/-- The two composites disagree already on 1: their values are 1 and 0. -/
theorem rankTwo_generator_not_commutes :
    action 0 (crossing 0 0) * rightOperator 0 (generator 0) ≠
      rightOperator 0 (generator 0) * action 0 (crossing 0 0) := by
  intro h
  have he := congrArg (fun T : Module.End ℤ (SkewPolynomial 2) => T 1) h
  rw [action_crossing] at he
  simp only [end_mul_apply, rightOperator_apply, one_mul, divided_one, zero_mul] at he
  have hx : divided (n := 0) 0 (generator (0 : Fin 2)) = 1 := by
    simp [divided_generator]
  have hz : (1 : SkewPolynomial 2) = 0 := hx.symm.trans he
  exact generator_ne_zero 0 0 (by
    calc
      (generator 0 : SkewPolynomial 2) = generator 0 * 1 := (mul_one _).symm
      _ = 0 := by rw [hz, mul_zero])

end OddMath.Frontier.NilHeckeRightKernel
