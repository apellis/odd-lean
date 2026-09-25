import OddMath.Frontier.EKRadicalQuotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Integral EK coideal and quotient coalgebra

EK 1107.5610v2, pp.7–8, (2.2)–(2.3), Proposition 2.3 (coideal)
and Corollary 2.4 (coalgebra), over ℤ at q = -1.
Every helper below serves coproduct_radical_zero or its literal coideal and
coalgebra descent consumers. No perfectness or integral global basis is assumed.
-/
noncomputable section
open scoped TensorProduct BigOperators
namespace OddMath.Frontier.EKCoideal
open CompleteElementary EKFreeCoproduct EKPairingAdjoint EKRadicalQuotient

/-- Nondegeneracy into ℤ implies torsion-freeness of the actual quotient. -/
instance quotient_noZeroSMulDivisors : NoZeroSMulDivisors ℤ Q where
  eq_zero_or_eq_zero_of_smul_eq_zero := by
    intro r x h
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    apply quotientPairing_nondegenerate_left
    intro y
    have hh := congrArg (fun z => quotientPairing z y) h
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, map_zero,
      LinearMap.zero_apply] at hh
    exact (mul_eq_zero.mp hh).resolve_left hr

/-- The actual quotient map on the integer tensor product. -/
def quotientTensorMap : T →ₗ[ℤ] Q ⊗[ℤ] Q :=
  TensorProduct.map piAlg.toLinearMap piAlg.toLinearMap

@[simp] theorem quotientTensorMap_tmul (x y : A) :
    quotientTensorMap (x ⊗ₜ[ℤ] y) = pi x ⊗ₜ[ℤ] pi y := rfl

/-- Evaluation of the unsigned tensor pairing against a pure tensor. -/
def tensorTest (a b : Q) : Q ⊗[ℤ] Q →ₗ[ℤ] ℤ :=
  TensorProduct.lift ((LinearMap.mul ℤ ℤ).compl₁₂
    (quotientPairing.flip a) (quotientPairing.flip b))

@[simp] theorem tensorTest_tmul (a b x y : Q) :
    tensorTest a b (x ⊗ₜ[ℤ] y) = quotientPairing x a * quotientPairing y b := rfl

/-- Integer tensor separation. Each individual tensor lifts from a finite
submodule of the first factor. That submodule is free by the PID theorem, not
by an assumption on the EK form. Pairing once reduces to a linear combination
of its independent basis vectors; pairing twice kills each coefficient. -/
theorem tensor_separation (z : Q ⊗[ℤ] Q)
    (hz : ∀ a b : Q, tensorTest a b z = 0) : z = 0 := by
  classical
  obtain ⟨M, hM, hm⟩ := TensorProduct.exists_finite_submodule_left_of_finite
    ({z} : Set (Q ⊗[ℤ] Q)) (Set.finite_singleton z)
  letI : Module.Finite ℤ M := hM
  obtain ⟨w, hw⟩ := hm (Set.mem_singleton z)
  obtain ⟨n, B⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_left B w
  have hw' : (∑ i : Fin n, (B i : Q) ⊗ₜ[ℤ] c i) = z := by
    rw [← hw, ← hc]
    simp [Finsupp.sum_fintype, LinearMap.rTensor, TensorProduct.map_tmul]
  have hcoeff (b : Q) : ∀ i : Fin n, quotientPairing (c i) b = 0 := by
    have hv : (∑ i : Fin n, quotientPairing (c i) b • (B i : Q)) = 0 := by
      apply quotientPairing_nondegenerate_left
      intro a
      have hh := hz a b
      rw [← hw'] at hh
      simpa only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, tensorTest_tmul, mul_comm] using hh
    have hi := B.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
    exact (Fintype.linearIndependent_iff.mp hi) _ hv
  have hc0 : ∀ i : Fin n, c i = 0 := by
    intro i
    exact quotientPairing_nondegenerate_left (c i) (fun b => hcoeff b i)
  rw [← hw']
  simp [hc0]

/-- Evaluation commutes with quotienting both tensor factors. -/
theorem tensorTest_map (a b : A) (z : T) :
    tensorTest (pi a) (pi b) (quotientTensorMap z) = tensorPairing z (a ⊗ₜ[ℤ] b) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, RingHom.map_zero,
      TensorProduct.zero_tmul, LinearMap.zero_apply, Submodule.Quotient.mk_zero]
  | tmul x y => simp
  | add x y hx hy => simp [hx, hy]

/-- The first genuine coideal inference: annihilation implies quotient zero. -/
theorem coproduct_radical_zero {x : A} (hx : x ∈ radical) :
    quotientTensorMap (coproduct x) = 0 := by
  apply tensor_separation
  intro a b
  obtain ⟨a, rfl⟩ := pi_surjective a
  obtain ⟨b, rfl⟩ := pi_surjective b
  rw [tensorTest_map]
  exact coproduct_radical_annihilates hx _

/-- Literal sum of the two subtype-embedded tensor ideals. -/
def coidealSubmodule : Submodule ℤ T :=
  LinearMap.range (TensorProduct.map (radical.restrictScalars ℤ).subtype
    (LinearMap.id : A →ₗ[ℤ] A)) ⊔
  LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[ℤ] A)
    (radical.restrictScalars ℤ).subtype)

/-- Quotient exactness, with no flatness assumption: both factors are quotiented. -/
theorem quotientTensorMap_eq_zero_iff (z : T) :
    quotientTensorMap z = 0 ↔ z ∈ coidealSubmodule := by
  let e := TensorProduct.quotientTensorQuotientEquiv
    (radical.restrictScalars ℤ) (radical.restrictScalars ℤ)
  have he : e (quotientTensorMap z) = Submodule.Quotient.mk z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, RingHom.map_zero,
      TensorProduct.zero_tmul, LinearMap.zero_apply, Submodule.Quotient.mk_zero]
    | tmul x y => rfl
    | add x y hx hy => simp only [LinearMap.map_add, LinearEquiv.map_add, RingHom.map_add, hx, hy, Submodule.Quotient.mk_add]
  rw [← e.map_eq_zero_iff, he]
  exact Submodule.Quotient.mk_eq_zero coidealSubmodule

/-- Proposition 2.3, coideal portion on the actual free algebra and radical. -/
theorem coproduct_mem_coideal {x : A} (hx : x ∈ radical) :
    coproduct x ∈ coidealSubmodule :=
  (quotientTensorMap_eq_zero_iff _).mp (coproduct_radical_zero hx)

/-- Genuine integer coproduct on the radical quotient. -/
def quotientCoproduct : Q →ₗ[ℤ] Q ⊗[ℤ] Q :=
  (radical.restrictScalars ℤ).liftQ (quotientTensorMap.comp coproduct)
    (fun _ hx => coproduct_radical_zero hx)

@[simp] theorem quotientCoproduct_pi (x : A) :
    quotientCoproduct (pi x) = quotientTensorMap (coproduct x) := rfl

private theorem assoc_quotient (t : T) (y : A) :
    TensorProduct.assoc ℤ Q Q Q (quotientTensorMap t ⊗ₜ[ℤ] pi y) =
    TensorProduct.map piAlg.toLinearMap quotientTensorMap
      (TensorProduct.assoc ℤ A A A (t ⊗ₜ[ℤ] y)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, RingHom.map_zero,
      TensorProduct.zero_tmul, LinearMap.zero_apply, Submodule.Quotient.mk_zero]
  | tmul a b => simp
  | add a b ha hb => simp only [LinearMap.map_add, LinearEquiv.map_add, RingHom.map_add, TensorProduct.add_tmul, ha, hb]

private theorem left_iterated_map (z : T) :
    TensorProduct.assoc ℤ Q Q Q
      (TensorProduct.map quotientCoproduct LinearMap.id (quotientTensorMap z)) =
    TensorProduct.map piAlg.toLinearMap quotientTensorMap
      (TensorProduct.assoc ℤ A A A (TensorProduct.map coproduct LinearMap.id z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, RingHom.map_zero,
      TensorProduct.zero_tmul, LinearMap.zero_apply, Submodule.Quotient.mk_zero]
  | tmul x y =>
    simpa only [quotientTensorMap_tmul, TensorProduct.map_tmul,
      quotientCoproduct_pi, LinearMap.id_apply] using assoc_quotient (coproduct x) y
  | add x y hx hy => simp only [LinearMap.map_add, LinearEquiv.map_add, RingHom.map_add, hx, hy]

private theorem right_iterated_map (z : T) :
    TensorProduct.map LinearMap.id quotientCoproduct (quotientTensorMap z) =
    TensorProduct.map piAlg.toLinearMap quotientTensorMap
      (TensorProduct.map LinearMap.id coproduct z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, RingHom.map_zero,
      TensorProduct.zero_tmul, LinearMap.zero_apply, Submodule.Quotient.mk_zero]
  | tmul x y => simp
  | add x y hx hy => simp only [LinearMap.map_add, LinearEquiv.map_add, RingHom.map_add, hx, hy]

/-- Coassociativity with the genuine tensor associator, on every quotient class. -/
theorem quotient_coassociativity (x : Q) :
    TensorProduct.assoc ℤ Q Q Q
      (TensorProduct.map quotientCoproduct LinearMap.id (quotientCoproduct x)) =
    TensorProduct.map LinearMap.id quotientCoproduct (quotientCoproduct x) := by
  obtain ⟨x, rfl⟩ := pi_surjective x
  rw [quotientCoproduct_pi, left_iterated_map, right_iterated_map,
    EKFreeCoproduct.coassociativity]

private theorem left_counit_map (z : T) :
    TensorProduct.lid ℤ Q
      (TensorProduct.map quotientCounit.toLinearMap LinearMap.id (quotientTensorMap z)) =
    pi (leftCounit z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, RingHom.map_zero,
      TensorProduct.zero_tmul, LinearMap.zero_apply, Submodule.Quotient.mk_zero]
  | tmul x y =>
    simp only [quotientTensorMap_tmul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      quotientCounit_pi, LinearMap.id_apply, TensorProduct.lid_tmul, leftCounit_tmul]
    exact (piAlg.toLinearMap.map_smul (counit x) y).symm
  | add x y hx hy => simp only [LinearMap.map_add, LinearEquiv.map_add, RingHom.map_add, hx, hy]

private theorem right_counit_map (z : T) :
    TensorProduct.rid ℤ Q
      (TensorProduct.map LinearMap.id quotientCounit.toLinearMap (quotientTensorMap z)) =
    pi (rightCounit z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero, RingHom.map_zero,
      TensorProduct.zero_tmul, LinearMap.zero_apply, Submodule.Quotient.mk_zero]
  | tmul x y =>
    simp only [quotientTensorMap_tmul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
      quotientCounit_pi, LinearMap.id_apply, TensorProduct.rid_tmul, rightCounit_tmul]
    exact (piAlg.toLinearMap.map_smul (counit y) x).symm
  | add x y hx hy => simp only [LinearMap.map_add, LinearEquiv.map_add, RingHom.map_add, hx, hy]

/-- Left counit law using the inherited actual quotient counit. -/
theorem quotient_counit_left (x : Q) :
    TensorProduct.lid ℤ Q
      (TensorProduct.map quotientCounit.toLinearMap LinearMap.id (quotientCoproduct x)) = x := by
  obtain ⟨x, rfl⟩ := pi_surjective x
  rw [quotientCoproduct_pi, left_counit_map, (counit_laws x).1]

/-- Right counit law using the inherited actual quotient counit. -/
theorem quotient_counit_right (x : Q) :
    TensorProduct.rid ℤ Q
      (TensorProduct.map LinearMap.id quotientCounit.toLinearMap (quotientCoproduct x)) = x := by
  obtain ⟨x, rfl⟩ := pi_surjective x
  rw [quotientCoproduct_pi, right_counit_map, (counit_laws x).2]

end OddMath.Frontier.EKCoideal
