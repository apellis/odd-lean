import OddMath.Frontier.SignedPermutation
import OddMath.Frontier.TwistedLeibniz
import Mathlib.Data.Matrix.Notation

/-! # Genuine all-rank odd divided differences
EKL arXiv:1111.1320v1 §2.1.1 (2.1)–(2.5), pp.3–4.
The matrix evaluation descends through the actual relation ideal before PBW transport.
-/
namespace OddMath.Frontier.AllRankDivided
open PbwL2 PbwL3
open OddMath.SkewPolynomial (SkewPolynomial generator)
variable {n : ℕ}

noncomputable def s (i : Fin (n+1)) : SkewPolynomial (n+2) ≃+* SkewPolynomial (n+2) :=
  SignedPermutation.skewAction (Equiv.swap i.castSucc i.succ)

theorem adjacent_ne (i : Fin (n+1)) : i.castSucc ≠ i.succ := by
  intro h
  have := congrArg Fin.val h
  change i.val = i.val + 1 at this
  omega

noncomputable def delta (i : Fin (n+1)) (j : Fin (n+2)) : Presented (n+2) :=
  if j = i.castSucc ∨ j = i.succ then 1 else 0

noncomputable def matrixGenerator (i : Fin (n+1)) (j : Fin (n+2)) :
    Matrix (Fin 2) (Fin 2) (Presented (n+2)) :=
  !![-q (n+2) (Equiv.swap i.castSucc i.succ j), delta i j; 0, q (n+2) j]

noncomputable def freeMatrix (i : Fin (n+1)) : FreeAlgebra ℤ (Fin (n+2)) →ₐ[ℤ]
    Matrix (Fin 2) (Fin 2) (Presented (n+2)) :=
  FreeAlgebra.lift ℤ (matrixGenerator i)

@[simp] theorem freeMatrix_ι (i : Fin (n+1)) (j : Fin (n+2)) :
    freeMatrix i (FreeAlgebra.ι ℤ j) = matrixGenerator i j := by
  simp [freeMatrix]

theorem freeMatrix_entries (i : Fin (n+1)) (w : FreeAlgebra ℤ (Fin (n+2))) :
    (freeMatrix i w) 1 0 = 0 ∧
    (freeMatrix i w) 0 0 = SignedPermutation.quotientEval
      (Equiv.swap i.castSucc i.succ) w ∧
    (freeMatrix i w) 1 1 = Ideal.Quotient.mk (relIdeal (n+2)) w := by
  induction w using FreeAlgebra.induction with
  | grade0 r =>
      simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply,
        ← Matrix.diagonal_intCast, Matrix.diagonal_apply]
  | grade1 j =>
      simp [matrixGenerator, SignedPermutation.quotientEval_ι,
        SignedPermutation.epsilon, Equiv.Perm.sign_swap (adjacent_ne i), q]
  | add a b ha hb => simp [map_add, Matrix.add_apply, ha, hb]
  | mul a b ha hb =>
      simp [map_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]

theorem matrixGenerator_rel (i : Fin (n+1)) (j k : Fin (n+2)) (h : j ≠ k) :
    matrixGenerator i j * matrixGenerator i k +
      matrixGenerator i k * matrixGenerator i j = 0 := by
  ext a b
  fin_cases a <;> fin_cases b
  · simpa [matrixGenerator, Matrix.mul_apply, Fin.sum_univ_two] using
      rel_sum (n+2) (Equiv.swap i.castSucc i.succ j)
        (Equiv.swap i.castSucc i.succ k) ((Equiv.swap _ _).injective.ne h)
  · by_cases hjl : j = i.castSucc <;> by_cases hjr : j = i.succ <;>
      by_cases hkl : k = i.castSucc <;> by_cases hkr : k = i.succ <;>
      simp_all [matrixGenerator, delta, Matrix.mul_apply, Fin.sum_univ_two,
        Equiv.swap_apply_def, adjacent_ne]
  · simp [matrixGenerator, Matrix.mul_apply, Fin.sum_univ_two]
  · simpa [matrixGenerator, Matrix.mul_apply, Fin.sum_univ_two] using rel_sum (n+2) j k h

theorem freeMatrix_kill_mem (i : Fin (n+1)) (w : FreeAlgebra ℤ (Fin (n+2)))
    (hw : w ∈ relIdeal (n+2)) : freeMatrix i w = 0 := by
  rw [relIdeal, relTwoSided, TwoSidedIdeal.mem_asIdeal] at hw
  induction hw using TwoSidedIdeal.span_induction with
  | mem x h =>
      obtain ⟨j, k, hjk, rfl⟩ := h
      simpa only [map_add, map_mul, freeMatrix_ι] using matrixGenerator_rel i j k hjk
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | neg x hx ih => rw [map_neg, ih, neg_zero]
  | left_absorb a x hx ih => rw [map_mul, ih, mul_zero]
  | right_absorb b x hx ih => rw [map_mul, ih, zero_mul]

noncomputable def presentedMatrix (i : Fin (n+1)) : Presented (n+2) →+*
    Matrix (Fin 2) (Fin 2) (Presented (n+2)) :=
  Ideal.Quotient.lift (relIdeal (n+2)) (freeMatrix i).toRingHom (freeMatrix_kill_mem i)

@[simp] theorem presentedMatrix_mk (i : Fin (n+1)) (w : FreeAlgebra ℤ (Fin (n+2))) :
    presentedMatrix i (Ideal.Quotient.mk (relIdeal (n+2)) w) = freeMatrix i w := rfl

theorem presentedMatrix_entries (i : Fin (n+1)) (x : Presented (n+2)) :
    (presentedMatrix i x) 1 0 = 0 ∧
    (presentedMatrix i x) 0 0 = SignedPermutation.presentedHom
      (Equiv.swap i.castSucc i.succ) x ∧
    (presentedMatrix i x) 1 1 = x := by
  induction x using Quotient.inductionOn' with
  | h w => exact freeMatrix_entries i w

/-- Upper-right entry of the genuine free-algebra matrix evaluation. -/
noncomputable def freeDivided (i : Fin (n+1)) :
    FreeAlgebra ℤ (Fin (n+2)) →ₗ[ℤ] Presented (n+2) where
  toFun w := freeMatrix i w 0 1
  map_add' a b := by simp [map_add]
  map_smul' c a := by
    change freeMatrix i (c • a) 0 1 = c • freeMatrix i a 0 1
    rw [map_smul]
    rfl

noncomputable def quotientMap : FreeAlgebra ℤ (Fin (n+2)) →+* Presented (n+2) :=
  Ideal.Quotient.mk (relIdeal (n+2))

theorem freeDivided_mul (i : Fin (n+1)) (a b : FreeAlgebra ℤ (Fin (n+2))) :
    freeDivided i (a*b) = freeDivided i a * quotientMap b +
      SignedPermutation.quotientEval (Equiv.swap i.castSucc i.succ) a * freeDivided i b := by
  change (freeMatrix i (a*b)) 0 1 = _
  simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two,
    (freeMatrix_entries i a).2.1, (freeMatrix_entries i b).2.2]
  exact add_comm _ _

theorem freeDivided_kill_mem (i : Fin (n+1)) (w : FreeAlgebra ℤ (Fin (n+2)))
    (hw : w ∈ relIdeal (n+2)) : freeDivided i w = 0 := by
  change freeMatrix i w 0 1 = 0
  rw [freeMatrix_kill_mem i w hw]
  rfl

/-- Quotient descent is established for the entire matrix, not posited. -/
noncomputable def presentedDivided (i : Fin (n+1)) : Presented (n+2) →ₗ[ℤ] Presented (n+2) where
  toFun x := presentedMatrix i x 0 1
  map_add' a b := by simp [map_add]
  map_smul' c a := by
    change presentedMatrix i (c • a) 0 1 = c • presentedMatrix i a 0 1
    rw [map_zsmul]
    rfl

@[simp] theorem presentedDivided_one (i : Fin (n+1)) : presentedDivided i 1 = 0 := by
  change presentedMatrix i 1 0 1 = 0
  simp [Matrix.one_apply]

@[simp] theorem presentedDivided_q (i : Fin (n+1)) (j : Fin (n+2)) :
    presentedDivided i (q (n+2) j) = delta i j := by
  change freeMatrix i (FreeAlgebra.ι ℤ j) 0 1 = _
  simp [matrixGenerator]

theorem presentedDivided_mul (i : Fin (n+1)) (x y : Presented (n+2)) :
    presentedDivided i (x*y) = presentedDivided i x*y +
      SignedPermutation.presentedHom (Equiv.swap i.castSucc i.succ) x * presentedDivided i y := by
  change presentedMatrix i (x*y) 0 1 = _
  simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two,
    (presentedMatrix_entries i x).2.1, (presentedMatrix_entries i y).2.2]
  exact add_comm _ _

/-- Conjugate the descended linear operator through the actual PBW equivalence. -/
noncomputable def divided (i : Fin (n+1)) :
    SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2) :=
  (PbwEquivalence.coefficientEquiv (n+2)).toLinearMap.comp
    ((presentedDivided i).comp (PbwEquivalence.coefficientEquiv (n+2)).symm.toLinearMap)

theorem divided_Phi (i : Fin (n+1)) (x : Presented (n+2)) :
    divided i (Phi (n+2) x) = Phi (n+2) (presentedDivided i x) := by
  change Phi (n+2) (presentedDivided i (PbwEquivalence.lift (n+2) (Phi (n+2) x))) = _
  rw [PbwEquivalence.lift_Phi]

/-- Explicit compatibility with the parent's ring equivalence, not a new PBW map. -/
theorem divided_presentedEquiv (i : Fin (n+1)) (x : Presented (n+2)) :
    divided i (PbwEquivalence.presentedEquiv (n+2) x) =
      PbwEquivalence.presentedEquiv (n+2) (presentedDivided i x) :=
  divided_Phi i x

theorem divided_one (i : Fin (n+1)) : divided i 1 = 0 := by
  rw [← map_one (Phi (n+2)), divided_Phi, presentedDivided_one, map_zero]

theorem divided_generator (i : Fin (n+1)) (j : Fin (n+2)) :
    divided i (generator j) = if j = i.castSucc ∨ j = i.succ then 1 else 0 := by
  rw [← Phi_q (n+2) j, divided_Phi, presentedDivided_q]
  simp only [delta]
  split <;> simp

theorem divided_mul (i : Fin (n+1)) (f g : SkewPolynomial (n+2)) :
    divided i (f*g) = divided i f*g + s i f*divided i g := by
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective (n+2) f
  obtain ⟨y, rfl⟩ := PbwRealization.Phi_surjective (n+2) g
  rw [← map_mul, divided_Phi, presentedDivided_mul, map_add, map_mul, map_mul,
    divided_Phi, divided_Phi]
  rw [s, SignedPermutation.action_Phi]

/-- The laws determine the operator on arbitrary integer skew polynomials. -/
theorem divided_unique (i : Fin (n+1))
    (D : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2))
    (h1 : D 1 = 0)
    (hgen : ∀ j, D (generator j) = if j = i.castSucc ∨ j = i.succ then 1 else 0)
    (hmul : ∀ f g, D (f*g) = D f*g + s i f*D g) : D = divided i := by
  apply LinearMap.ext
  intro f
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective (n+2) f
  induction x using Quotient.inductionOn' with
  | h w =>
      change D (evalAlg (n+2) w) = divided i (evalAlg (n+2) w)
      induction w using FreeAlgebra.induction with
      | grade0 r =>
          rw [AlgHom.commutes]
          change D (r • 1) = divided i (r • 1)
          rw [map_smul, map_smul, h1, divided_one]
      | grade1 j => rw [evalAlg_ι, hgen, divided_generator]
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
      | mul a b ha hb => rw [map_mul, hmul, divided_mul, ha, hb]

/-- The inherited closed-sum rank-two operator, bundled but not redefined. -/
noncomputable def rankTwoLinear : SkewPolynomial 2 →ₗ[ℤ] SkewPolynomial 2 where
  toFun := DividedDifferences.div1
  map_add' := DividedDifferences.div1_add
  map_smul' c f := (TwistedLeibniz.D.map_zsmul f c)

theorem rankTwo_eq_div1 (f : SkewPolynomial 2) :
    divided (0 : Fin 1) f = DividedDifferences.div1 f := by
  have h : rankTwoLinear = divided (0 : Fin 1) := by
    apply divided_unique
    · exact DividedDifferences.div1_one
    · intro j
      fin_cases j
      · exact DividedDifferences.div1_generator_zero
      · exact DividedDifferences.div1_generator_one
    · intro a b
      change DividedDifferences.div1 (a*b) = _
      rw [show s (0 : Fin 1) a = DividedDifferences.symm1 a from
        SignedPermutation.action_swap_eq_symm1 a]
      exact TwistedLeibniz.div1_mul a b
  exact (LinearMap.congr_fun h f).symm

theorem s_generator (i : Fin (n+1)) (j : Fin (n+2)) :
    s i (generator j) = -generator (Equiv.swap i.castSucc i.succ j) :=
  SignedPermutation.action_swap_generator _ _ (adjacent_ne i) j

theorem divided_left_mul (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i (generator i.castSucc * f) = f - generator i.succ * divided i f := by
  rw [divided_mul, divided_generator, s_generator]
  simp [sub_eq_add_neg]

theorem divided_right_mul (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i (generator i.succ * f) = f - generator i.castSucc * divided i f := by
  rw [divided_mul, divided_generator, s_generator]
  simp [sub_eq_add_neg]

theorem divided_spectator_mul (i : Fin (n+1)) (j : Fin (n+2))
    (hl : j ≠ i.castSucc) (hr : j ≠ i.succ) (f : SkewPolynomial (n+2)) :
    divided i (generator j * f) = -generator j * divided i f := by
  rw [divided_mul, divided_generator, s_generator]
  simp [hl, hr, Equiv.swap_apply_of_ne_of_ne hl hr]

theorem divided_mul_left (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i (f * generator i.castSucc) = divided i f * generator i.castSucc + s i f := by
  rw [divided_mul, divided_generator]
  simp

theorem divided_mul_right (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i (f * generator i.succ) = divided i f * generator i.succ + s i f := by
  rw [divided_mul, divided_generator]
  simp

theorem divided_mul_spectator (i : Fin (n+1)) (j : Fin (n+2))
    (hl : j ≠ i.castSucc) (hr : j ≠ i.succ) (f : SkewPolynomial (n+2)) :
    divided i (f * generator j) = divided i f * generator j := by
  rw [divided_mul, divided_generator]
  simp [hl, hr]

end OddMath.Frontier.AllRankDivided
