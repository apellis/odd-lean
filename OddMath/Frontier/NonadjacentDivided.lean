import OddMath.Frontier.AllRankDivided

/-! EKL 1111.1320v1 p15 (2.59)--(2.61). Arbitrary distinct endpoints.
Concrete upper triangular matrix evaluation kills the real two-sided relation
ideal; PBW transports its upper-right entry to actual integer skew polynomials.
-/
namespace OddMath.Frontier.NonadjacentDivided
open PbwL2 PbwL3
open OddMath.SkewPolynomial (SkewPolynomial generator)
variable {n : ℕ}

noncomputable def s (u v : Fin (n+2)) :
    SkewPolynomial (n+2) ≃+* SkewPolynomial (n+2) :=
  SignedPermutation.skewAction (Equiv.swap u v)

noncomputable def delta (u v : Fin (n+2)) (_huv : u ≠ v) (j : Fin (n+2)) : Presented (n+2) :=
  if j = u ∨ j = v then 1 else 0

noncomputable def matrixGenerator (u v : Fin (n+2)) (huv : u ≠ v) (j : Fin (n+2)) :
    Matrix (Fin 2) (Fin 2) (Presented (n+2)) :=
  !![-q (n+2) (Equiv.swap u v j), delta u v huv j; 0, q (n+2) j]

noncomputable def freeMatrix (u v : Fin (n+2)) (huv : u ≠ v) : FreeAlgebra ℤ (Fin (n+2)) →ₐ[ℤ]
    Matrix (Fin 2) (Fin 2) (Presented (n+2)) :=
  FreeAlgebra.lift ℤ (matrixGenerator u v huv)

@[simp] theorem freeMatrix_ι (u v : Fin (n+2)) (huv : u ≠ v) (j : Fin (n+2)) :
    freeMatrix u v huv (FreeAlgebra.ι ℤ j) = matrixGenerator u v huv j := by
  simp [freeMatrix]

theorem freeMatrix_entries (u v : Fin (n+2)) (huv : u ≠ v) (w : FreeAlgebra ℤ (Fin (n+2))) :
    (freeMatrix u v huv w) 1 0 = 0 ∧
    (freeMatrix u v huv w) 0 0 = SignedPermutation.quotientEval
      (Equiv.swap u v) w ∧
    (freeMatrix u v huv w) 1 1 = Ideal.Quotient.mk (relIdeal (n+2)) w := by
  induction w using FreeAlgebra.induction with
  | grade0 r =>
      simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply,
        ← Matrix.diagonal_intCast, Matrix.diagonal_apply]
  | grade1 j =>
      simp [matrixGenerator, SignedPermutation.quotientEval_ι,
        SignedPermutation.epsilon, Equiv.Perm.sign_swap huv, q]
  | add a b ha hb => simp [map_add, Matrix.add_apply, ha, hb]
  | mul a b ha hb =>
      simp [map_mul, Matrix.mul_apply, Fin.sum_univ_two, ha, hb]

theorem matrixGenerator_rel (u v : Fin (n+2)) (huv : u ≠ v) (j k : Fin (n+2)) (h : j ≠ k) :
    matrixGenerator u v huv j * matrixGenerator u v huv k +
      matrixGenerator u v huv k * matrixGenerator u v huv j = 0 := by
  ext a b
  fin_cases a <;> fin_cases b
  · simpa [matrixGenerator, Matrix.mul_apply, Fin.sum_univ_two] using
      rel_sum (n+2) (Equiv.swap u v j)
        (Equiv.swap u v k) ((Equiv.swap _ _).injective.ne h)
  · by_cases hjl : j = u <;> by_cases hjr : j = v <;>
      by_cases hkl : k = u <;> by_cases hkr : k = v <;>
      simp_all [matrixGenerator, delta, Matrix.mul_apply, Fin.sum_univ_two,
        Equiv.swap_apply_def, huv]
  · simp [matrixGenerator, Matrix.mul_apply, Fin.sum_univ_two]
  · simpa [matrixGenerator, Matrix.mul_apply, Fin.sum_univ_two] using rel_sum (n+2) j k h

theorem freeMatrix_kill_mem (u v : Fin (n+2)) (huv : u ≠ v) (w : FreeAlgebra ℤ (Fin (n+2)))
    (hw : w ∈ relIdeal (n+2)) : freeMatrix u v huv w = 0 := by
  rw [relIdeal, relTwoSided, TwoSidedIdeal.mem_asIdeal] at hw
  induction hw using TwoSidedIdeal.span_induction with
  | mem x h =>
      obtain ⟨j, k, hjk, rfl⟩ := h
      simpa only [map_add, map_mul, freeMatrix_ι] using matrixGenerator_rel u v huv j k hjk
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
  | neg x hx ih => rw [map_neg, ih, neg_zero]
  | left_absorb a x hx ih => rw [map_mul, ih, mul_zero]
  | right_absorb b x hx ih => rw [map_mul, ih, zero_mul]

noncomputable def presentedMatrix (u v : Fin (n+2)) (huv : u ≠ v) : Presented (n+2) →+*
    Matrix (Fin 2) (Fin 2) (Presented (n+2)) :=
  Ideal.Quotient.lift (relIdeal (n+2)) (freeMatrix u v huv).toRingHom (freeMatrix_kill_mem u v huv)

@[simp] theorem presentedMatrix_mk (u v : Fin (n+2)) (huv : u ≠ v) (w : FreeAlgebra ℤ (Fin (n+2))) :
    presentedMatrix u v huv (Ideal.Quotient.mk (relIdeal (n+2)) w) = freeMatrix u v huv w := rfl

theorem presentedMatrix_entries (u v : Fin (n+2)) (huv : u ≠ v) (x : Presented (n+2)) :
    (presentedMatrix u v huv x) 1 0 = 0 ∧
    (presentedMatrix u v huv x) 0 0 = SignedPermutation.presentedHom
      (Equiv.swap u v) x ∧
    (presentedMatrix u v huv x) 1 1 = x := by
  induction x using Quotient.inductionOn' with
  | h w => exact freeMatrix_entries u v huv w

/-- Upper-right entry of the genuine free-algebra matrix evaluation. -/
noncomputable def freeDivided (u v : Fin (n+2)) (huv : u ≠ v) :
    FreeAlgebra ℤ (Fin (n+2)) →ₗ[ℤ] Presented (n+2) where
  toFun w := freeMatrix u v huv w 0 1
  map_add' a b := by simp [map_add]
  map_smul' c a := by
    change freeMatrix u v huv (c • a) 0 1 = c • freeMatrix u v huv a 0 1
    rw [map_smul]
    rfl

noncomputable def quotientMap : FreeAlgebra ℤ (Fin (n+2)) →+* Presented (n+2) :=
  Ideal.Quotient.mk (relIdeal (n+2))

theorem freeDivided_mul (u v : Fin (n+2)) (huv : u ≠ v) (a b : FreeAlgebra ℤ (Fin (n+2))) :
    freeDivided u v huv (a*b) = freeDivided u v huv a * quotientMap b +
      SignedPermutation.quotientEval (Equiv.swap u v) a * freeDivided u v huv b := by
  change (freeMatrix u v huv (a*b)) 0 1 = _
  simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two,
    (freeMatrix_entries u v huv a).2.1, (freeMatrix_entries u v huv b).2.2]
  exact add_comm _ _

theorem freeDivided_kill_mem (u v : Fin (n+2)) (huv : u ≠ v) (w : FreeAlgebra ℤ (Fin (n+2)))
    (hw : w ∈ relIdeal (n+2)) : freeDivided u v huv w = 0 := by
  change freeMatrix u v huv w 0 1 = 0
  rw [freeMatrix_kill_mem u v huv w hw]
  rfl

/-- Quotient descent is established for the entire matrix, not posited. -/
noncomputable def presentedDivided (u v : Fin (n+2)) (huv : u ≠ v) : Presented (n+2) →ₗ[ℤ] Presented (n+2) where
  toFun x := presentedMatrix u v huv x 0 1
  map_add' a b := by simp [map_add]
  map_smul' c a := by
    change presentedMatrix u v huv (c • a) 0 1 = c • presentedMatrix u v huv a 0 1
    rw [map_zsmul]
    rfl

@[simp] theorem presentedDivided_one (u v : Fin (n+2)) (huv : u ≠ v) : presentedDivided u v huv 1 = 0 := by
  change presentedMatrix u v huv 1 0 1 = 0
  simp [Matrix.one_apply]

@[simp] theorem presentedDivided_q (u v : Fin (n+2)) (huv : u ≠ v) (j : Fin (n+2)) :
    presentedDivided u v huv (q (n+2) j) = delta u v huv j := by
  change freeMatrix u v huv (FreeAlgebra.ι ℤ j) 0 1 = _
  simp [matrixGenerator]

theorem presentedDivided_mul (u v : Fin (n+2)) (huv : u ≠ v) (x y : Presented (n+2)) :
    presentedDivided u v huv (x*y) = presentedDivided u v huv x*y +
      SignedPermutation.presentedHom (Equiv.swap u v) x * presentedDivided u v huv y := by
  change presentedMatrix u v huv (x*y) 0 1 = _
  simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_two,
    (presentedMatrix_entries u v huv x).2.1, (presentedMatrix_entries u v huv y).2.2]
  exact add_comm _ _

/-- Conjugate the descended linear operator through the actual PBW equivalence. -/
noncomputable def dividedPair (u v : Fin (n+2)) (huv : u ≠ v) :
    SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2) :=
  (PbwEquivalence.coefficientEquiv (n+2)).toLinearMap.comp
    ((presentedDivided u v huv).comp (PbwEquivalence.coefficientEquiv (n+2)).symm.toLinearMap)

theorem divided_Phi (u v : Fin (n+2)) (huv : u ≠ v) (x : Presented (n+2)) :
    dividedPair u v huv (Phi (n+2) x) = Phi (n+2) (presentedDivided u v huv x) := by
  change Phi (n+2) (presentedDivided u v huv (PbwEquivalence.lift (n+2) (Phi (n+2) x))) = _
  rw [PbwEquivalence.lift_Phi]

/-- Explicit compatibility with the parent's ring equivalence, not a new PBW map. -/
theorem divided_presentedEquiv (u v : Fin (n+2)) (huv : u ≠ v) (x : Presented (n+2)) :
    dividedPair u v huv (PbwEquivalence.presentedEquiv (n+2) x) =
      PbwEquivalence.presentedEquiv (n+2) (presentedDivided u v huv x) :=
  divided_Phi u v huv x

theorem divided_one (u v : Fin (n+2)) (huv : u ≠ v) : dividedPair u v huv 1 = 0 := by
  rw [← map_one (Phi (n+2)), divided_Phi, presentedDivided_one, map_zero]

theorem divided_generator (u v : Fin (n+2)) (huv : u ≠ v) (j : Fin (n+2)) :
    dividedPair u v huv (generator j) = if j = u ∨ j = v then 1 else 0 := by
  rw [← Phi_q (n+2) j, divided_Phi, presentedDivided_q]
  simp only [delta]
  split <;> simp

theorem divided_mul (u v : Fin (n+2)) (huv : u ≠ v) (f g : SkewPolynomial (n+2)) :
    dividedPair u v huv (f*g) = dividedPair u v huv f*g + s u v f*dividedPair u v huv g := by
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective (n+2) f
  obtain ⟨y, rfl⟩ := PbwRealization.Phi_surjective (n+2) g
  rw [← map_mul, divided_Phi, presentedDivided_mul, map_add, map_mul, map_mul,
    divided_Phi, divided_Phi]
  rw [s, SignedPermutation.action_Phi]

/-- The laws determine the operator on arbitrary integer skew polynomials. -/
theorem divided_unique (u v : Fin (n+2)) (huv : u ≠ v)
    (D : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2))
    (h1 : D 1 = 0)
    (hgen : ∀ j, D (generator j) = if j = u ∨ j = v then 1 else 0)
    (hmul : ∀ f g, D (f*g) = D f*g + s u v f*D g) : D = dividedPair u v huv := by
  apply LinearMap.ext
  intro f
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective (n+2) f
  induction x using Quotient.inductionOn' with
  | h w =>
      change D (evalAlg (n+2) w) = dividedPair u v huv (evalAlg (n+2) w)
      induction w using FreeAlgebra.induction with
      | grade0 r =>
          rw [AlgHom.commutes]
          change D (r • 1) = dividedPair u v huv (r • 1)
          rw [map_smul, map_smul, h1, divided_one]
      | grade1 j => rw [evalAlg_ι, hgen, divided_generator]
      | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
      | mul a b ha hb => rw [map_mul, hmul, divided_mul, ha, hb]


/-- Unitality is forced by the Leibniz rule, not an extra assumption. -/
theorem unique (u v : Fin (n+2)) (huv : u ≠ v)
    (D : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2))
    (hgen : ∀ j, D (generator j) = if j = u ∨ j = v then 1 else 0)
    (hmul : ∀ f g, D (f*g) = D f*g + s u v f*D g) : D = dividedPair u v huv := by
  apply divided_unique u v huv D _ hgen hmul
  have h := hmul 1 1
  simp only [one_mul, mul_one, map_one] at h
  exact (add_eq_left.mp h.symm)

/-- Exchange of endpoints does not change the source operator. -/
theorem symmetric (u v : Fin (n+2)) (huv : u ≠ v) :
    dividedPair u v huv = dividedPair v u huv.symm := by
  apply unique
  · intro j
    simp only [divided_generator, or_comm]
  · intro f g
    simpa only [s, Equiv.swap_comm v u] using divided_mul u v huv f g

/-- Genuine adjacent specialization on every polynomial. -/
theorem adjacent (i : Fin (n+1)) :
    dividedPair i.castSucc i.succ (AllRankDivided.adjacent_ne i) =
      AllRankDivided.divided i := by
  apply AllRankDivided.divided_unique
  · exact divided_one _ _ _
  · exact divided_generator _ _ _
  · exact divided_mul _ _ _

/-- The presentation supplies induction over all integer skew polynomials. -/
theorem polynomial_induction {P : SkewPolynomial (n+2) → Prop}
    (hconst : ∀ r : ℤ, P (r • 1)) (hgen : ∀ j, P (generator j))
    (hadd : ∀ f g, P f → P g → P (f+g))
    (hmul : ∀ f g, P f → P g → P (f*g)) (f : SkewPolynomial (n+2)) : P f := by
  obtain ⟨x, rfl⟩ := PbwRealization.Phi_surjective (n+2) f
  induction x using Quotient.inductionOn' with
  | h w =>
    change P (evalAlg (n+2) w)
    induction w using FreeAlgebra.induction with
    | grade0 r => simpa only [AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
        map_smul, map_one] using hconst r
    | grade1 j => simpa only [evalAlg_ι] using hgen j
    | add a b ha hb => simpa only [map_add] using hadd _ _ ha hb
    | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb

/-- The conjugation permutation identity includes the global signs. -/
theorem action_conjugation (u v k l : Fin (n+2)) (f : SkewPolynomial (n+2)) :
    s u v (s k l f) = s k l (s (Equiv.swap k l u) (Equiv.swap k l v) f) := by
  have hp : Equiv.swap u v * Equiv.swap k l =
      Equiv.swap k l * Equiv.swap (Equiv.swap k l u) (Equiv.swap k l v) := by
    apply Equiv.ext
    intro h
    simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_self] using
      ((Equiv.swap k l).injective.map_swap (Equiv.swap k l u) (Equiv.swap k l v) h).symm
  simpa only [s, SignedPermutation.action_mul] using
    congrArg (fun p => SignedPermutation.skewAction p f) hp

/-- Literal EKL (2.60), with transported endpoints and the minus sign. -/
theorem covariance (u v k l : Fin (n+2)) (huv : u ≠ v) (hkl : k ≠ l)
    (f : SkewPolynomial (n+2)) :
    dividedPair u v huv (s k l f) =
      -s k l (dividedPair (Equiv.swap k l u) (Equiv.swap k l v)
        ((Equiv.swap k l).injective.ne huv) f) := by
  induction f using polynomial_induction with
  | hconst r => simp only [map_zsmul, map_smul, map_one, divided_one, smul_zero, map_zero, neg_zero]
  | hgen j =>
    rw [show s k l (generator j) = -generator (Equiv.swap k l j) from
      SignedPermutation.action_swap_generator k l hkl j, map_neg, divided_generator,
      divided_generator]
    simp only [Equiv.swap_apply_eq_iff]
    split_ifs <;> simp_all
  | hadd f g hf hg => simp only [map_add, hf, hg, neg_add_rev, add_comm]
  | hmul f g hf hg =>
    simp only [map_mul, divided_mul, map_add, hf, hg, action_conjugation u v k l f]
    noncomm_ring

/-- Disjoint endpoints specialize (2.60) without changing the operator. -/
theorem covariance_disjoint (u v k l : Fin (n+2)) (huv : u ≠ v) (hkl : k ≠ l)
    (huk : u ≠ k) (hul : u ≠ l) (hvk : v ≠ k) (hvl : v ≠ l)
    (f : SkewPolynomial (n+2)) :
    dividedPair u v huv (s k l f) = -s k l (dividedPair u v huv f) := by
  simpa only [Equiv.swap_apply_of_ne_of_ne huk hul,
    Equiv.swap_apply_of_ne_of_ne hvk hvl] using covariance u v k l huv hkl f

/-- Disjoint transpositions commute on the actual globally signed polynomial action. -/
theorem action_disjoint (u v k l : Fin (n+2))
    (huk : u ≠ k) (hul : u ≠ l) (hvk : v ≠ k) (hvl : v ≠ l)
    (f : SkewPolynomial (n+2)) : s u v (s k l f) = s k l (s u v f) := by
  simpa only [Equiv.swap_apply_of_ne_of_ne huk hul,
    Equiv.swap_apply_of_ne_of_ne hvk hvl] using action_conjugation u v k l f

/-- EKL Lemma 2.19(2), (2.61), for every integral skew polynomial. -/
theorem anticommutation (u v k l : Fin (n+2)) (huv : u ≠ v) (hkl : k ≠ l)
    (huk : u ≠ k) (hul : u ≠ l) (hvk : v ≠ k) (hvl : v ≠ l)
    (f : SkewPolynomial (n+2)) :
    dividedPair u v huv (dividedPair k l hkl f) =
      -dividedPair k l hkl (dividedPair u v huv f) := by
  induction f using polynomial_induction with
  | hconst r => simp only [map_smul, divided_one, smul_zero, map_zero, neg_zero]
  | hgen j =>
    simp only [divided_generator]
    split_ifs <;> simp only [divided_one, map_zero, neg_zero]
  | hadd f g hf hg => simp only [map_add, hf, hg, neg_add_rev, add_comm]
  | hmul f g hf hg =>
    simp only [divided_mul, map_add,
      covariance_disjoint u v k l huv hkl huk hul hvk hvl,
      covariance_disjoint k l u v hkl huv huk.symm hvk.symm hul.symm hvl.symm,
      action_disjoint u v k l huk hul hvk hvl, hf, hg]
    noncomm_ring

end OddMath.Frontier.NonadjacentDivided
