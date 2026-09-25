import OddMath.Frontier.NilHeckeEndomorphism
import OddMath.Frontier.NilHeckeRightKernel

namespace OddMath.Frontier.NilHeckeEndomorphismControls
open NilHeckeAction AllRankDivided
open OddMath.SkewPolynomial (SkewPolynomial generator)
noncomputable section

-- Hand-derived N=2 coordinates in (1,x₀): D extracts the x₀ coefficient.
def e00 : Presented 0 := 1 - dot 0 0 * crossing 0 0
def e01 : Presented 0 := crossing 0 0
def e10 : Presented 0 := dot 0 0 * e00
def e11 : Presented 0 := dot 0 0 * crossing 0 0

theorem rankTwo_units :
    action 0 e00 1 = 1 ∧ action 0 e00 (generator 0) = 0 ∧
    action 0 e01 1 = 0 ∧ action 0 e01 (generator 0) = 1 ∧
    action 0 e10 1 = generator 0 ∧ action 0 e10 (generator 0) = 0 ∧
    action 0 e11 1 = 0 ∧ action 0 e11 (generator 0) = generator 0 := by
  simp [e00, e01, e10, e11, action_mul_apply, action_dot_apply,
    action_crossing, divided_one, divided_generator]

theorem rankTwo_projector (k l : OddSymmetricKernel.kernelSubring 0) :
    action 0 e00 ((k : SkewPolynomial 2) + generator 0 * (l : SkewPolynomial 2)) = k := by
  have h0 := NilHeckeRightKernel.action_right_mul_kernel 0 e00 k 1
  have h1 := NilHeckeRightKernel.action_right_mul_kernel 0 e00 l (generator 0)
  rw [map_add, show action 0 e00 (k : SkewPolynomial 2) = k by
    simpa [rankTwo_units.1] using h0, h1, rankTwo_units.2.1, zero_mul, add_zero]

def k1 : SkewPolynomial 2 := generator 0 - generator 1
def k2 : SkewPolynomial 2 := generator 0 * generator 1

theorem k1_kernel : k1 ∈ OddSymmetricKernel.kernelSubring 0 :=
  NilHeckeRightKernel.rankTwo_difference_mem

theorem k2_kernel : k2 ∈ OddSymmetricKernel.kernelSubring 0 := by
  rw [OddSymmetricKernel.mem_kernelSubring]
  intro i
  have hi : i = 0 := Fin.ext (by have h := i.isLt; omega)
  subst i
  simp [k2, divided_mul, divided_generator, s_generator]

-- Noncommuting kernel coefficients reject a silent opposite-ring switch.
theorem kernel_noncommuting : k1 * k2 ≠ k2 * k1 := by
  intro h
  have he := congrArg (fun f : SkewPolynomial 2 => f ![2,1]) h
  have mm (a b : Fin 2 → ℕ) (r s : ℤ) :
      OddMath.SkewPolynomial.monomial a r * OddMath.SkewPolynomial.monomial b s =
      OddMath.SkewPolynomial.monomial (a+b) (r*s*OddMath.skewSign a b) :=
    OddMath.SkewPolynomial.mul_monomial a b r s
  simp only [k1, k2, sub_mul, mul_sub, generator, mm] at he
  norm_num [OddMath.SkewPolynomial.monomial, OddMath.SkewPolynomial.expSingle,
    OddMath.skewSign, OddMath.crossingCount, Fin.sum_univ_two,
    Finset.sum_filter, funext_iff, Fin.forall_fin_two] at he
  have ha : OddMath.SkewPolynomial.expSingle (0 : Fin 2) +
      (OddMath.SkewPolynomial.expSingle 0 + OddMath.SkewPolynomial.expSingle 1) = ![2,1] := by
    funext i; fin_cases i <;> simp [OddMath.SkewPolynomial.expSingle]
  have hb : OddMath.SkewPolynomial.expSingle (0 : Fin 2) +
      OddMath.SkewPolynomial.expSingle 1 + OddMath.SkewPolynomial.expSingle 0 = ![2,1] := by
    funext i; fin_cases i <;> simp [OddMath.SkewPolynomial.expSingle]
  rw [ha, hb, Finsupp.single_eq_same] at he
  norm_num at he

-- These direct acceptance consumers are deliberately AFTER production.
open NilHeckeEndomorphism NilCoxeterWords OddSchubertAction
open scoped BigOperators

theorem arbitrary_endomorphism (n : ℕ) (T : rightKernelEnd n) :
    ∃! a : Presented n, ∀ f, action n a f = T.val f := by
  obtain ⟨a,ha⟩ := restrictedAction_surjective n T
  refine ⟨a, ?_, ?_⟩
  · intro f
    exact congrArg (fun U : rightKernelEnd n => U.val f) ha
  · intro b hb
    apply NilHeckeBasis.action_injective n
    apply LinearMap.ext
    intro f
    exact (hb f).trans (congrArg (fun U : rightKernelEnd n => U.val f) ha).symm

theorem arbitrary_matrix (n : ℕ) (M : Matrix (Perm n) (Perm n) (K n)) :
    ∃ a : Presented n, ∀ i j,
      coordinates n (action n a (schubert j)) i = M i j := by
  obtain ⟨T,hT⟩ := (matrixEquiv n).surjective M
  obtain ⟨a,ha⟩ := (actionEquiv n).surjective T
  refine ⟨a, ?_⟩
  intro i j
  have h := congrFun (congrFun hT i) j
  rw [← ha] at h
  exact h

-- Composition order is witnessed with genuinely noncommuting coefficients.
theorem diagonal_order_negative :
    let a : K 0 := ⟨k1,k1_kernel⟩
    let b : K 0 := ⟨k2,k2_kernel⟩
    a * b ≠ b * a := by
  dsimp only
  intro h
  exact kernel_noncommuting (congrArg Subtype.val h)

end
end OddMath.Frontier.NilHeckeEndomorphismControls
