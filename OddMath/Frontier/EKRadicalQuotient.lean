import OddMath.Frontier.EKPairingAdjoint
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual EK radical and its integer algebra quotient

Ellis–Khovanov 1107.5610v2, pp.7–8, (2.1)–(2.3), Proposition 2.3
(ideal part) and Corollary 2.4 (algebra part), at integers and q = -1.
The radical is the annihilator of the inherited source-matched form, not an
ideal given by generators. Tensor annihilation below is NOT a coideal theorem:
tensor-radical identification and coproduct descent remain open.
-/
noncomputable section
open scoped TensorProduct
namespace OddMath.Frontier.EKRadicalQuotient
open CompleteElementary EKFreeCoproduct EKPairingAdjoint

/-- Vanishing against all tensors follows by genuine tensor induction. -/
private theorem tensor_annihilates_left {x : A} (hx : ∀ y, pairing x y = 0)
    (a : A) (z : T) : tensorPairing (x ⊗ₜ[ℤ] a) z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b c => simp [hx]
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]

private theorem tensor_annihilates_right {x : A} (hx : ∀ y, pairing x y = 0)
    (a : A) (z : T) : tensorPairing (a ⊗ₜ[ℤ] x) z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b c => simp [hx]
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]

/-- Left ideal on precisely the source's annihilator predicate. -/
def radical : Ideal A where
  carrier := {x | ∀ y, pairing x y = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy z
    change ∀ z, pairing x z = 0 at hx
    change ∀ z, pairing y z = 0 at hy
    simp only [map_add, LinearMap.add_apply, hx, hy, add_zero]
  smul_mem' := by
    intro a x hx y
    change pairing (a*x) y = 0
    rw [← adjointness]
    exact tensor_annihilates_right hx a (coproduct y)

@[simp] theorem mem_radical (x : A) : x ∈ radical ↔ ∀ y, pairing x y = 0 := Iff.rfl

/-- Arbitrary left factors, not merely generators or homogeneous elements. -/
theorem radical_mul_left (a : A) {x : A} (hx : x ∈ radical) : a*x ∈ radical :=
  radical.mul_mem_left a hx

/-- Arbitrary right factors; adjointness uses the other tensor slot. -/
theorem radical_mul_right {x : A} (hx : x ∈ radical) (a : A) : x*a ∈ radical := by
  intro y
  rw [← adjointness]
  exact tensor_annihilates_left hx a (coproduct y)

instance : radical.IsTwoSided where
  mul_mem_of_left a hx := radical_mul_right hx a

/-- The genuine quotient ring of the actual free algebra by its radical. -/
abbrev Q := A ⧸ radical

/-- Canonical quotient ring homomorphism. -/
def pi : A →+* Q := Ideal.Quotient.mk radical

theorem pi_surjective : Function.Surjective pi := Ideal.Quotient.mk_surjective

@[simp] theorem pi_eq_zero_iff (x : A) : pi x = 0 ↔ x ∈ radical :=
  Ideal.Quotient.eq_zero_iff_mem

/-- Explicit integer algebra structure and quotient algebra map. -/
def piAlg : A →ₐ[ℤ] Q := Ideal.Quotient.mkₐ ℤ radical

@[simp] theorem piAlg_apply (x : A) : piAlg x = pi x := rfl

/-- Descend the second slot using symmetry of the actual integer form. -/
private def pairingRight (x : A) : Q →ₗ[ℤ] ℤ :=
  (radical.restrictScalars ℤ).liftQ (pairing x) (by
    intro y hy
    change pairing x y = 0
    rw [pairing_symm]
    exact hy x)

private theorem pairingRight_pi (x y : A) : pairingRight x (pi y) = pairing x y := rfl

private def pairingToQuotient : A →ₗ[ℤ] Q →ₗ[ℤ] ℤ where
  toFun := pairingRight
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := pi_surjective z
    simp only [LinearMap.add_apply, pairingRight_pi, map_add]
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := pi_surjective z
    simp only [LinearMap.smul_apply, pairingRight_pi, map_smul, RingHom.id_apply]

/-- Integer bilinear form on the actual quotient; both lifts are proved. -/
def quotientPairing : Q →ₗ[ℤ] Q →ₗ[ℤ] ℤ :=
  (radical.restrictScalars ℤ).liftQ pairingToQuotient (by
    intro x hx
    apply LinearMap.ext
    intro y
    obtain ⟨y, rfl⟩ := pi_surjective y
    exact hx y)

@[simp] theorem quotientPairing_pi (x y : A) :
    quotientPairing (pi x) (pi y) = pairing x y := rfl

theorem quotientPairing_symm (x y : Q) : quotientPairing x y = quotientPairing y x := by
  obtain ⟨x, rfl⟩ := pi_surjective x
  obtain ⟨y, rfl⟩ := pi_surjective y
  exact pairing_symm x y

/-- Nondegeneracy means trivial annihilator, not integral perfectness. -/
theorem quotientPairing_nondegenerate_left (x : Q)
    (hx : ∀ y : Q, quotientPairing x y = 0) : x = 0 := by
  obtain ⟨x, rfl⟩ := pi_surjective x
  apply (pi_eq_zero_iff x).mpr
  intro y
  exact hx (pi y)

theorem quotientPairing_nondegenerate_right (y : Q)
    (hy : ∀ x : Q, quotientPairing x y = 0) : y = 0 := by
  apply quotientPairing_nondegenerate_left y
  intro x
  rw [quotientPairing_symm]
  exact hy x

/-- The actual source counit is pairing against the unit. -/
theorem counit_radical {x : A} (hx : x ∈ radical) : counit x = 0 := by
  rw [← pairing_right_one]
  exact hx 1

/-- Counit descends as an integer algebra homomorphism, hence also a ring map. -/
def quotientCounit : Q →ₐ[ℤ] ℤ :=
  Ideal.Quotient.liftₐ radical counitAlg (fun _ hx => counit_radical hx)

@[simp] theorem quotientCounit_pi (x : A) : quotientCounit (pi x) = counit x := rfl

theorem quotientPairing_right_one (x : Q) : quotientPairing x 1 = quotientCounit x := by
  obtain ⟨x, rfl⟩ := pi_surjective x
  rw [← pi.map_one, quotientPairing_pi, quotientCounit_pi, pairing_right_one]

/-- Only tensor-form annihilation. No identification with the sum of tensor
radicals, and no descended coproduct or bialgebra structure, is asserted. -/
theorem coproduct_radical_annihilates {x : A} (hx : x ∈ radical) (z : T) :
    tensorPairing (coproduct x) z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [tensorPairing_symm, adjointness, pairing_symm]
    exact hx (a*b)
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]

end OddMath.Frontier.EKRadicalQuotient
