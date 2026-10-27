import OddMath.SKM.UniversalCoefficientReduced

/-! The dependent roots `(2,-1)` retain nonzero order-two torsion.
Their rational group algebra and its exact coefficient-slot polynomial ring
are reduced but have nonzero zero divisors. -/

noncomputable section
namespace NonVacuity.UniversalCoefficientReduced
open OddMath.SKM
open OddMath.SKM.NormalizationParameterGroup
open OddMath.SKM.UniversalCoefficientReduced

/-- Roots `(2,-1)` in the original weight group ℤ; the second colour is odd. -/
def datum : Datum Bool ℤ where
  cd := {
    root := fun i => if i then -1 else 2
    coroot := fun i => (if i then -2 else 1) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)
    coroot_root_self := by intro i; cases i <;> norm_num }
  isGCM := {
    diag := by intro i; cases i <;> norm_num [CartanDatum.cartanMatrix_apply]
    offDiag_nonpos := by
      intro i j h
      cases i <;> cases j <;> simp_all [CartanDatum.cartanMatrix_apply]
    zero_comm := by
      intro i j
      cases i <;> cases j <;> norm_num [CartanDatum.cartanMatrix_apply] }
  parity := fun i => if i then 1 else 0
  even_of_odd := by
    intro i j hi
    cases i
    · simp at hi
    · cases j
      · exact ⟨-2, by norm_num⟩
      · exact ⟨1, by norm_num⟩

/-- Positive symmetrizers `(4,1)`. -/
def symmetrizer : Symmetrizer datum where
  d := fun i => if i then 1 else 4
  pos := by intro i; cases i <;> norm_num
  symm := by intro i j; cases i <;> cases j <;> norm_num [Datum.d, Datum.h, Datum.α, datum]

/-- A unit retaining both components of the order-two parameter. -/
def u : (ℚ × ℚ)ˣ where
  val := (1, -1)
  inv := (1, -1)
  val_inv := by ext <;> norm_num
  inv_val := by ext <;> norm_num

theorem u_sq : u ^ 2 = 1 := by ext <;> norm_num [u]

theorem u_inv : u⁻¹ = u := by ext <;> norm_num [u]

theorem u_ne_one : u ≠ 1 := by
  intro h
  have := congrArg (fun z : (ℚ × ℚ)ˣ => (z : ℚ × ℚ).2) h
  norm_num [u] at this

theorem u_ne_neg_one : (u : ℚ × ℚ) ≠ -1 := by
  intro h
  have := congrArg Prod.fst h
  norm_num [u] at this

def scalars : Scalars datum (ℚ × ℚ) where
  t := fun i j => if i then 1 else if j then u else 1
  t_self := by intro i; cases i <;> rfl
  t_symm_of_d_eq_zero := by
    intro i j h
    cases i <;> cases j <;> norm_num [Datum.d, Datum.h, Datum.α, datum] at h
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by
    intro _
    refine ⟨⟨2, (1/2, 1/2), ?_, ?_⟩, rfl⟩ <;> ext <;> norm_num

theorem homogeneous : scalars.Homogeneous :=
  fun _ _ _ _ _ _ _ _ h => (h rfl).elim

/-- Since `u²=1`, using `u^μ` also equals the formula `u^(-μ)` in §2. -/
def normalizations : CScalars scalars where
  c := fun μ i => if i then 1 else u ^ μ
  shift := by
    intro μ i j
    cases i <;> cases j
    · change u ^ (μ + (2 : ℤ)) = 1 * u ^ μ
      rw [zpow_add]
      simp [u_sq]
    · change u ^ (μ + (-1 : ℤ)) = u * u ^ μ
      rw [zpow_add]
      simp [u_inv, mul_comm]
    · simp [scalars]
    · simp [scalars]

/-- The concrete supplied units are images of the actual presented generators. -/
example : (specialize normalizations (t datum false true)).toMul = u :=
  specialize_t normalizations false true

example (μ : ℤ) : (specialize normalizations (c datum μ false)).toMul = u ^ μ :=
  specialize_c normalizations μ false

/-- Lifting the universal generators recovers the identity, including its torsion. -/
example : lift datum (t datum) (c datum) (t_self datum) (t_symm datum) (c_shift datum) =
    AddMonoidHom.id (Group datum) := by
  apply hom_ext <;> intros <;> simp

/-- The root dependency forces order dividing two, inside the quotient itself. -/
theorem endpoint_add_self : t datum false true + t datum false true = 0 := by
  have h₂ := c_shift datum 0 false false
  have h₁ := c_shift datum 2 false true
  have h₀ := c_shift datum 1 false true
  change c datum 2 false = t datum false false + c datum 0 false at h₂
  rw [t_self, zero_add] at h₂
  change c datum 1 false = t datum false true + c datum 2 false at h₁
  change c datum 0 false = t datum false true + c datum 1 false at h₀
  apply add_right_cancel (b := c datum 0 false)
  calc
    (t datum false true + t datum false true) + c datum 0 false =
        t datum false true + c datum 1 false := by rw [h₁, h₂, add_assoc]
    _ = 0 + c datum 0 false := by rw [← h₀, zero_add]

/-- Specialization proves that this torsion was not killed by saturation. -/
theorem endpoint_ne_zero : t datum false true ≠ 0 := by
  intro h
  have hh := congrArg (specialize normalizations) h
  have hu : Additive.ofMul u = 0 := by simpa [specialize, scalars] using hh
  exact u_ne_one (congrArg Additive.toMul hu)

abbrev GroupRing := AddMonoidAlgebra ℚ (Group datum)
abbrev Parameters := MvPolynomial (UniversalPolynomialParameters.Slot datum) GroupRing

/-- The group-algebra monomial of the nonzero order-two endpoint. -/
def endpoint : GroupRing := AddMonoidAlgebra.single (t datum false true) 1

theorem endpoint_sq : endpoint ^ 2 = 1 := by
  simp [endpoint, pow_two, AddMonoidAlgebra.single_mul_single, endpoint_add_self,
    ← AddMonoidAlgebra.one_def]

theorem endpoint_sub_one_ne_zero : endpoint - 1 ≠ 0 := by
  intro h
  have hc := congrArg (fun f : GroupRing => f.coeff (t datum false true)) h
  simp [endpoint, AddMonoidAlgebra.one_def, endpoint_ne_zero] at hc

theorem endpoint_add_one_ne_zero : endpoint + 1 ≠ 0 := by
  intro h
  have hc := congrArg (fun f : GroupRing => f.coeff (t datum false true)) h
  simp [endpoint, AddMonoidAlgebra.one_def, endpoint_ne_zero] at hc

theorem endpoint_factors_mul : (endpoint - 1) * (endpoint + 1) = 0 := by
  calc
    _ = endpoint ^ 2 - 1 := by ring
    _ = 0 := by rw [endpoint_sq, sub_self]

theorem groupRing_reduced : IsReduced GroupRing := rationalGroupAlgebra_isReduced _

theorem parameters_reduced : IsReduced Parameters := rationalParameters_isReduced datum

/-- Reducedness does not discard the two nonzero factors in the polynomial ring. -/
theorem polynomial_zero_divisors :
    (MvPolynomial.C (endpoint - 1) : Parameters) ≠ 0 ∧
    (MvPolynomial.C (endpoint + 1) : Parameters) ≠ 0 ∧
    (MvPolynomial.C (endpoint - 1) : Parameters) * MvPolynomial.C (endpoint + 1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply endpoint_sub_one_ne_zero
    exact MvPolynomial.C_injective _ _ (h.trans (map_zero _).symm)
  · intro h
    apply endpoint_add_one_ne_zero
    exact MvPolynomial.C_injective _ _ (h.trans (map_zero _).symm)
  · rw [← map_mul, endpoint_factors_mul, map_zero]

/-- Arbitrary nilpotent polynomials vanish, not only constant polynomials. -/
theorem nilpotent_parameter_eq_zero (f : Parameters) (h : IsNilpotent f) : f = 0 := by
  let := parameters_reduced
  exact isNilpotent_iff_eq_zero.mp h

example (f : Parameters) (h : ∀ p, primeFractionMap Parameters p f = 0) : f = 0 :=
  rationalParameters_separate datum f h

#print axioms OddMath.SKM.UniversalCoefficientReduced.inversion
#print axioms OddMath.SKM.UniversalCoefficientReduced.coeff_inversion
#print axioms OddMath.SKM.UniversalCoefficientReduced.inversion_inversion
#print axioms OddMath.SKM.UniversalCoefficientReduced.coeff_mul_inversion
#print axioms OddMath.SKM.UniversalCoefficientReduced.eq_zero_of_mul_inversion_eq_zero
#print axioms OddMath.SKM.UniversalCoefficientReduced.rationalGroupAlgebra_isReduced
#print axioms OddMath.SKM.UniversalCoefficientReduced.rationalParameters_isReduced
#print axioms OddMath.SKM.UniversalCoefficientReduced.rationalParameters_separate
#print axioms endpoint_add_self
#print axioms endpoint_ne_zero
#print axioms endpoint_sq
#print axioms endpoint_sub_one_ne_zero
#print axioms endpoint_add_one_ne_zero
#print axioms endpoint_factors_mul
#print axioms groupRing_reduced
#print axioms parameters_reduced
#print axioms polynomial_zero_divisors
#print axioms nilpotent_parameter_eq_zero
end NonVacuity.UniversalCoefficientReduced
