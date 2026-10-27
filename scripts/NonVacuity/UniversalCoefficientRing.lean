import OddMath.SKM.UniversalCoefficientRing
import OddMath.SKM.Grading

/-! Evaluation of the normalization unit ring. The dependent-root data and
supplied ℚ × ℚ parameters are those of NormalizationParameterGroup's consumer.
The additional evaluations in ZMod 9 and ZMod 1 require neither a field nor
an embedding of ℚ. No polynomial coefficient extension is asserted here. -/

noncomputable section

namespace NonVacuity.UniversalCoefficientRing

open OddMath.SKM
open OddMath.SKM.UniversalCoefficientRing

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

theorem two_unit : IsUnit (2 : ℚ × ℚ) :=
  scalars.two_isUnit ⟨true, rfl⟩

/-- Evaluate the constructed ring, not just its abstract parameter group. -/
def evaluation : UnitRing datum →+* ℚ × ℚ := specialize two_unit normalizations

example : Units.map evaluation (t datum false true) = u :=
  specialize_t two_unit normalizations false true

example (μ : ℤ) : Units.map evaluation (c datum μ false) = u ^ μ :=
  specialize_c two_unit normalizations μ false

example : evaluation ((t datum false true : (UnitRing datum)ˣ) : UnitRing datum) = (1, -1) := by
  exact congrArg (fun z : (ℚ × ℚ)ˣ => (z : ℚ × ℚ))
    (specialize_t two_unit normalizations false true)

example : t datum false true ≠ 1 := by
  intro h
  apply u_ne_one
  simpa [h, scalars] using (specialize_t two_unit normalizations false true).symm

example : ((t datum false true : (UnitRing datum)ˣ) : UnitRing datum) ≠ -1 := by
  intro h
  apply u_ne_neg_one
  have he := congrArg (fun z : (ℚ × ℚ)ˣ => (z : ℚ × ℚ))
    (specialize_t two_unit normalizations false true)
  change evaluation _ = (u : ℚ × ℚ) at he
  simpa [h] using he.symm

example (f : UnitRing datum →+* ℚ × ℚ)
    (ht : ∀ i j, Units.map f (t datum i j) = scalars.t i j)
    (hc : ∀ μ i, Units.map f (c datum μ i) = normalizations.c μ i) :
    f = evaluation :=
  specialize_unique two_unit normalizations f ht hc

/-- Constant units also give admissible supplied parameters over rings with
zero divisors and in positive characteristic. -/
def constantScalars (R : Type*) [CommRing R] (h₂ : IsUnit (2 : R)) : Scalars datum R where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => h₂

def constantNormalizations (R : Type*) [CommRing R] (h₂ : IsUnit (2 : R)) :
    CScalars (constantScalars R h₂) where
  c := fun _ _ => 1
  shift := by intros; simp [constantScalars]

theorem two_unit_nine : IsUnit (2 : ZMod 9) := by
  refine ⟨⟨2, 5, ?_, ?_⟩, rfl⟩ <;> decide

example : Units.map (specialize two_unit_nine (constantNormalizations (ZMod 9) two_unit_nine)).toMonoidHom
    (t datum false true) = 1 :=
  specialize_t two_unit_nine _ false true

example (μ : ℤ) : Units.map
    (specialize two_unit_nine (constantNormalizations (ZMod 9) two_unit_nine)).toMonoidHom
    (c datum μ false) = 1 :=
  specialize_c two_unit_nine _ μ false

/-- The actual inverse of 2 in the localization evaluates to 5 modulo 9. -/
example : baseSpecialize two_unit_nine (IsLocalization.Away.invSelf (2 : ℤ)) = 5 := by
  have h := congrArg (baseSpecialize two_unit_nine)
    (IsLocalization.Away.mul_invSelf (S := HalfIntegers) (2 : ℤ))
  have h' : (2 : ZMod 9) * baseSpecialize two_unit_nine
      (IsLocalization.Away.invSelf (2 : ℤ)) = 1 := by
    simpa only [map_mul, map_one, baseSpecialize, IsLocalization.Away.lift_eq,
      map_ofNat] using h
  calc
    _ = (5 : ZMod 9) * (2 * baseSpecialize two_unit_nine
        (IsLocalization.Away.invSelf (2 : ℤ))) := by
      have h52 : (5 : ZMod 9) * 2 = 1 := by decide
      rw [← mul_assoc, h52, one_mul]
    _ = 5 := by rw [h', mul_one]

theorem two_unit_zero : IsUnit (2 : ZMod 1) := by
  have h : (2 : ZMod 1) = 1 := Subsingleton.elim _ _
  rw [h]
  exact isUnit_one

example : Units.map (specialize two_unit_zero (constantNormalizations (ZMod 1) two_unit_zero)).toMonoidHom
    (c datum 0 false) = 1 :=
  specialize_c two_unit_zero _ 0 false

#print axioms OddMath.SKM.UniversalCoefficientRing.two_isUnit_base
#print axioms OddMath.SKM.UniversalCoefficientRing.groupUnit
#print axioms OddMath.SKM.UniversalCoefficientRing.t_self
#print axioms OddMath.SKM.UniversalCoefficientRing.t_symm
#print axioms OddMath.SKM.UniversalCoefficientRing.c_shift
#print axioms OddMath.SKM.UniversalCoefficientRing.two_isUnit
#print axioms OddMath.SKM.UniversalCoefficientRing.baseSpecialize
#print axioms OddMath.SKM.UniversalCoefficientRing.base_hom_ext
#print axioms OddMath.SKM.UniversalCoefficientRing.lift
#print axioms OddMath.SKM.UniversalCoefficientRing.lift_groupUnit
#print axioms OddMath.SKM.UniversalCoefficientRing.hom_ext
#print axioms OddMath.SKM.UniversalCoefficientRing.specialize
#print axioms OddMath.SKM.UniversalCoefficientRing.specialize_t
#print axioms OddMath.SKM.UniversalCoefficientRing.specialize_c
#print axioms OddMath.SKM.UniversalCoefficientRing.specialize_unique

end NonVacuity.UniversalCoefficientRing
