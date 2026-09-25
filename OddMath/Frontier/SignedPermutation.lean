import OddMath.Frontier.PbwEquivalence
import OddMath.Frontier.SignedSwap
import Mathlib.GroupTheory.Perm.Sign

/-!
# The signed symmetric-group action on the actual integral odd polynomial ring

EKL arXiv:1111.1320v1 §2.1.1 (2.1)–(2.2), p.3. Every generator carries
Perm.sign, including spectators of a transposition. Products sigma*tau act
first by tau, then sigma. No square-zero relations are introduced.
-/

namespace OddMath.Frontier.SignedPermutation

open PbwL2 PbwL3
open OddMath.SkewPolynomial (SkewPolynomial generator)

variable {n : ℕ}

/-- The integer value of the genuine permutation sign. -/
def epsilon (sigma : Equiv.Perm (Fin n)) : ℤ := Equiv.Perm.sign sigma

@[simp] theorem epsilon_one : epsilon (1 : Equiv.Perm (Fin n)) = 1 := by
  simp [epsilon]

@[simp] theorem epsilon_mul (sigma tau : Equiv.Perm (Fin n)) :
    epsilon (sigma * tau) = epsilon sigma * epsilon tau := by
  simp [epsilon]

/-- Free evaluation at globally signed, permuted quotient generators. -/
noncomputable def quotientEval (sigma : Equiv.Perm (Fin n)) :
    FreeAlgebra ℤ (Fin n) →ₐ[ℤ] Presented n :=
  FreeAlgebra.lift ℤ (fun j => epsilon sigma • q n (sigma j))

@[simp] theorem quotientEval_ι (sigma : Equiv.Perm (Fin n)) (j : Fin n) :
    quotientEval sigma (FreeAlgebra.ι ℤ j) = epsilon sigma • q n (sigma j) := by
  simp [quotientEval]

/-- Off-diagonal relations are killed by the actual evaluation. -/
theorem quotientEval_kills (sigma : Equiv.Perm (Fin n)) (i j : Fin n) (h : i ≠ j) :
    quotientEval sigma (FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j +
      FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i) = 0 := by
  rw [map_add, map_mul, map_mul, quotientEval_ι, quotientEval_ι]
  simp only [smul_mul_assoc, mul_smul_comm, ← smul_add,
    rel_sum n (sigma i) (sigma j) (sigma.injective.ne h), smul_zero]

/-- Two-sided span induction, not an assumed factorization. -/
theorem kill_mem (sigma : Equiv.Perm (Fin n)) (w : FreeAlgebra ℤ (Fin n))
    (hw : w ∈ relIdeal n) : quotientEval sigma w = 0 := by
  rw [relIdeal, relTwoSided, TwoSidedIdeal.mem_asIdeal] at hw
  induction hw using TwoSidedIdeal.span_induction with
  | mem x h =>
      obtain ⟨i, j, hij, rfl⟩ := h
      exact quotientEval_kills sigma i j hij
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | neg x hx ih => rw [map_neg, ih, neg_zero]
  | left_absorb a x hx ih => rw [map_mul, ih, mul_zero]
  | right_absorb b x hx ih => rw [map_mul, ih, zero_mul]

/-- The map on the actual presented quotient. -/
noncomputable def presentedHom (sigma : Equiv.Perm (Fin n)) : Presented n →+* Presented n :=
  Ideal.Quotient.lift (relIdeal n) (quotientEval sigma).toRingHom (kill_mem sigma)

@[simp] theorem presentedHom_q (sigma : Equiv.Perm (Fin n)) (j : Fin n) :
    presentedHom sigma (q n j) = epsilon sigma • q n (sigma j) := by
  change quotientEval sigma (FreeAlgebra.ι ℤ j) = _
  exact quotientEval_ι sigma j

/-- Genuine generator extensionality, proved in the quotient universal property. -/
theorem presentedHom_ext {R : Type*} [Ring R] {f g : Presented n →+* R}
    (h : ∀ j, f (q n j) = g (q n j)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro w
  induction w using FreeAlgebra.induction with
  | grade0 r => simp
  | grade1 j => exact h j
  | mul a b ha hb => simpa only [map_mul] using congrArg₂ (· * ·) ha hb
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb

@[simp] theorem presentedHom_one :
    presentedHom (1 : Equiv.Perm (Fin n)) = RingHom.id (Presented n) := by
  apply presentedHom_ext
  intro j
  simp

/-- Multiplication orientation: the right permutation acts first. -/
theorem presentedHom_mul (sigma tau : Equiv.Perm (Fin n)) :
    presentedHom (sigma * tau) = (presentedHom sigma).comp (presentedHom tau) := by
  apply presentedHom_ext
  intro j
  simp only [presentedHom_q, RingHom.comp_apply, map_zsmul, epsilon_mul,
    Equiv.Perm.mul_apply, smul_smul]
  rw [Int.mul_comm]

/-- Invertibility follows from the proved composition law. -/
noncomputable def presentedAction (sigma : Equiv.Perm (Fin n)) :
    Presented n ≃+* Presented n where
  toFun := presentedHom sigma
  invFun := presentedHom sigma⁻¹
  left_inv x := by
    have h := RingHom.congr_fun (presentedHom_mul sigma⁻¹ sigma) x
    simpa only [inv_mul_cancel, presentedHom_one, RingHom.id_apply,
      RingHom.comp_apply] using h.symm
  right_inv x := by
    have h := RingHom.congr_fun (presentedHom_mul sigma sigma⁻¹) x
    simpa only [mul_inv_cancel, presentedHom_one, RingHom.id_apply,
      RingHom.comp_apply] using h.symm
  map_mul' := (presentedHom sigma).map_mul
  map_add' := (presentedHom sigma).map_add

@[simp] theorem presentedAction_apply (sigma : Equiv.Perm (Fin n)) (x : Presented n) :
    presentedAction sigma x = presentedHom sigma x := rfl

@[simp] theorem presentedAction_q (sigma : Equiv.Perm (Fin n)) (j : Fin n) :
    presentedAction sigma (q n j) = epsilon sigma • q n (sigma j) :=
  presentedHom_q sigma j

/-- Conjugation by the actual all-rank PBW equivalence, with its existing ring instances. -/
noncomputable def skewAction (sigma : Equiv.Perm (Fin n)) :
    SkewPolynomial n ≃+* SkewPolynomial n :=
  ((PbwEquivalence.presentedEquiv n).symm.trans (presentedAction sigma)).trans
    (PbwEquivalence.presentedEquiv n)

/-- Exact compatibility with the original quotient-to-model map. -/
theorem action_Phi (sigma : Equiv.Perm (Fin n)) (x : Presented n) :
    skewAction sigma (Phi n x) = Phi n (presentedHom sigma x) := by
  change PbwEquivalence.presentedEquiv n
    (presentedAction sigma ((PbwEquivalence.presentedEquiv n).symm
      (PbwEquivalence.presentedEquiv n x))) = _
  rw [RingEquiv.symm_apply_apply]
  rfl

/-- EKL's signed generator law in every rank. -/
@[simp] theorem action_generator (sigma : Equiv.Perm (Fin n)) (j : Fin n) :
    skewAction sigma (generator j) = epsilon sigma • generator (sigma j) := by
  rw [← Phi_q n j, action_Phi, presentedHom_q, map_zsmul, Phi_q]

@[simp] theorem action_one (f : SkewPolynomial n) :
    skewAction (1 : Equiv.Perm (Fin n)) f = f := by
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective n f
  rw [action_Phi, presentedHom_one, RingHom.id_apply]

/-- The group product acts first by tau and then by sigma on arbitrary inputs. -/
theorem action_mul (sigma tau : Equiv.Perm (Fin n)) (f : SkewPolynomial n) :
    skewAction (sigma * tau) f = skewAction sigma (skewAction tau f) := by
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective n f
  rw [action_Phi, action_Phi, action_Phi, presentedHom_mul, RingHom.comp_apply]

/-- Actual ring multiplication, not permutation composition. -/
theorem action_mul_polynomial (sigma : Equiv.Perm (Fin n)) (f g : SkewPolynomial n) :
    skewAction sigma (f * g) = skewAction sigma f * skewAction sigma g :=
  (skewAction sigma).map_mul f g

/-- Every generator is negated, including those fixed by the transposition. -/
theorem action_swap_generator (i j : Fin n) (h : i ≠ j) (k : Fin n) :
    skewAction (Equiv.swap i j) (generator k) = -generator ((Equiv.swap i j) k) := by
  rw [action_generator]
  simp [epsilon, Equiv.Perm.sign_swap h]

/-- Model ring maps are determined on generators by actual presentation surjectivity. -/
theorem skewHom_ext {R : Type*} [Ring R] {f g : SkewPolynomial n →+* R}
    (h : ∀ j, f (generator j) = g (generator j)) : f = g := by
  have he : f.comp (Phi n) = g.comp (Phi n) := by
    apply presentedHom_ext
    intro j
    simpa only [RingHom.comp_apply, Phi_q] using h j
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := PbwRealization.Phi_surjective n x
  exact RingHom.congr_fun he y

/-- Bundle the inherited symm1 without changing its definition.
Multiplicativity and involution are consumed from the signed-swap parent. -/
noncomputable def symm1Equiv : SkewPolynomial 2 ≃+* SkewPolynomial 2 where
  toFun := DividedDifferences.symm1
  invFun := DividedDifferences.symm1
  left_inv := SignedSwap.symm1_involute
  right_inv := SignedSwap.symm1_involute
  map_mul' := SignedSwap.symm1_mul
  map_add' := DividedDifferences.symm1_add

/-- The all-rank construction recovers the existing rank-two operator on every input. -/
theorem action_swap_eq_symm1 (f : SkewPolynomial 2) :
    skewAction (Equiv.swap (0 : Fin 2) 1) f = DividedDifferences.symm1 f := by
  have he : (skewAction (Equiv.swap (0 : Fin 2) 1)).toRingHom = symm1Equiv.toRingHom := by
    apply skewHom_ext
    intro j
    change skewAction (Equiv.swap (0 : Fin 2) 1) (generator j) =
      DividedDifferences.symm1 (generator j)
    rw [action_swap_generator 0 1 (by decide)]
    fin_cases j
    · simpa using DividedDifferences.symm1_generator_zero.symm
    · simpa using DividedDifferences.symm1_generator_one.symm
  exact RingHom.congr_fun he f

end OddMath.Frontier.SignedPermutation
