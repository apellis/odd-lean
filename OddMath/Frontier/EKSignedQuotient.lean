import OddMath.Frontier.EKCoideal

/-!
# EK signed multiplication on the actual integral radical quotient
EK 1107.5610v2 §2.1 pp.5–8, signed tensor rule, Prop.2.3 and Cor.2.4.
Only ℤ, q=-1. No arbitrary-q, explicit graded instance, or antipode claim.
-/
noncomputable section
open scoped TensorProduct BigOperators
namespace OddMath.Frontier.EKSignedQuotient
open CompleteElementary EKFreeCoproduct EKPairingAdjoint EKRadicalQuotient EKCoideal

/-- Degree-sign twist needed when a homogeneous word crosses an arbitrary factor. -/
def twist (n : ℕ) : A →ₗ[ℤ] A :=
  wordBasis.constr ℤ (fun w => (-1 : ℤ)^(degree w * n) • wordBasis w)

@[simp] theorem twist_basis (n : ℕ) (w : W) :
    twist n (wordBasis w) = (-1 : ℤ)^(degree w*n) • wordBasis w := by
  simp [twist]

theorem parts_sum (w : W) : (∑ i, parts w i) = degree w := by
  rw [← List.sum_ofFn]
  congr 1
  exact List.ext_get (by simp [parts]) (by intro i h₁ h₂; simp [parts])

theorem pairing_degree_zero (v w : W) (h : degree v ≠ degree w) :
    pairing (wordBasis v) (wordBasis w) = 0 := by
  rw [pairing_basis]
  exact EKPairingMatrices.pairing_degree_mismatch _ _ (by simpa only [parts_sum] using h)

/-- Orthogonality of different weights proves sign-twist self-adjointness. -/
theorem pairing_twist (n : ℕ) (x y : A) :
    pairing (twist n x) y = pairing x (twist n y) := by
  induction x using basis_induction wordBasis with
  | hz => simp
  | ha x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | hb v r =>
    induction y using basis_induction wordBasis with
    | hz => simp
    | ha x y hx hy => simp only [map_add, hx, hy]
    | hb w s =>
      simp only [map_smul, twist_basis, LinearMap.smul_apply, smul_eq_mul]
      by_cases h : degree v = degree w
      · rw [h]; ring
      · rw [pairing_degree_zero v w h]; ring

/-- Crucial descent inference: twisting the actual radical preserves it. -/
theorem twist_radical (n : ℕ) {x : A} (hx : x ∈ radical) : twist n x ∈ radical := by
  intro y
  rw [pairing_twist]
  exact hx _

/-- Multiply a basis tensor on the left; the second left factor crosses x. -/
theorem tensorMul_basis_tmul (a b : W) (x y : A) :
    tensorMul (tensorBasis (a,b)) (x ⊗ₜ[ℤ] y) =
      (wordBasis a * twist (degree b) x) ⊗ₜ[ℤ] (wordBasis b * y) := by
  induction x using basis_induction wordBasis with
  | hz => simp
  | ha x z hx hz => simp only [TensorProduct.add_tmul, tensorMul_add_right,
      map_add, mul_add, hx, hz]
  | hb c r =>
    induction y using basis_induction wordBasis with
    | hz => simp
    | ha y z hy hz => simp only [TensorProduct.tmul_add, tensorMul_add_right,
        map_add, mul_add, hy, hz]
    | hb d s =>
      simp only [map_smul, twist_basis, mul_smul_comm, TensorProduct.smul_tmul,
        TensorProduct.tmul_smul, tensorMul_smul_right]
      rw [← tensorBasis_apply, tensorMul_basis]
      simp only [tensorBasis_apply, wordBasis_mul, Prod.fst, Prod.snd,
        TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul]
      rw [Nat.mul_comm (degree c) (degree b)]

/-- Multiply a basis tensor on the right; y crosses the first right factor. -/
theorem tensorMul_tmul_basis (x y : A) (c d : W) :
    tensorMul (x ⊗ₜ[ℤ] y) (tensorBasis (c,d)) =
      (x * wordBasis c) ⊗ₜ[ℤ] (twist (degree c) y * wordBasis d) := by
  induction x using basis_induction wordBasis with
  | hz => simp
  | ha x z hx hz => simp only [TensorProduct.add_tmul, tensorMul_add_left,
      map_add, add_mul, hx, hz]
  | hb a r =>
    induction y using basis_induction wordBasis with
    | hz => simp
    | ha y z hy hz => simp only [TensorProduct.tmul_add, tensorMul_add_left,
        map_add, add_mul, hy, hz]
    | hb b s =>
      simp only [map_smul, twist_basis, smul_mul_assoc, TensorProduct.smul_tmul,
        TensorProduct.tmul_smul, tensorMul_smul_left]
      rw [← tensorBasis_apply, tensorMul_basis]
      simp only [tensorBasis_apply, wordBasis_mul, Prod.fst, Prod.snd,
        TensorProduct.smul_tmul, TensorProduct.tmul_smul, smul_smul]
      congr 1
      ring

/-- The literal tensor-ideal description lets any linear annihilator descend. -/
theorem kills_tensor_kernel {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : T →ₗ[ℤ] M)
    (h₁ : ∀ x ∈ radical, ∀ y, f (x ⊗ₜ[ℤ] y) = 0)
    (h₂ : ∀ y ∈ radical, ∀ x, f (x ⊗ₜ[ℤ] y) = 0)
    {z : T} (hz : quotientTensorMap z = 0) : f z = 0 := by
  have hle : coidealSubmodule ≤ LinearMap.ker f := by
    apply sup_le
    · rintro _ ⟨t, rfl⟩
      change f (TensorProduct.map (radical.restrictScalars ℤ).subtype LinearMap.id t) = 0
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simpa using h₁ x x.property y
      | add a b ha hb => simp only [map_add, ha, hb, add_zero]
    · rintro _ ⟨t, rfl⟩
      change f (TensorProduct.map LinearMap.id (radical.restrictScalars ℤ).subtype t) = 0
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simpa using h₂ y y.property x
      | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  exact hle ((quotientTensorMap_eq_zero_iff z).mp hz)

/-- Kernel stability for left multiplication by arbitrary actual free tensors. -/
theorem tensor_kernel_mul_right (x : T) {z : T} (hz : quotientTensorMap z = 0) :
    quotientTensorMap (tensorMul x z) = 0 := by
  induction x using basis_induction tensorBasis with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_left, map_add, hx, hy, add_zero]
  | hb p r =>
    simp only [tensorMul_smul_left, map_smul]
    suffices quotientTensorMap (tensorMul (tensorBasis p) z) = 0 by rw [this, smul_zero]
    apply kills_tensor_kernel (quotientTensorMap.comp (tensorMulLinear (tensorBasis p))) ?_ ?_ hz
    · intro a ha b
      change quotientTensorMap (tensorMul (tensorBasis p) (a ⊗ₜ[ℤ] b)) = 0
      rw [tensorMul_basis_tmul, quotientTensorMap_tmul,
        (pi_eq_zero_iff _).mpr (radical_mul_left _ (twist_radical _ ha)), TensorProduct.zero_tmul]
    · intro b hb a
      change quotientTensorMap (tensorMul (tensorBasis p) (a ⊗ₜ[ℤ] b)) = 0
      rw [tensorMul_basis_tmul, quotientTensorMap_tmul,
        (pi_eq_zero_iff _).mpr (radical_mul_left _ hb), TensorProduct.tmul_zero]

/-- Kernel stability for right multiplication, including the crossed radical factor. -/
theorem tensor_kernel_mul_left {z : T} (hz : quotientTensorMap z = 0) (y : T) :
    quotientTensorMap (tensorMul z y) = 0 := by
  induction y using basis_induction tensorBasis with
  | hz => simp
  | ha x y hx hy => simp only [tensorMul_add_right, map_add, hx, hy, add_zero]
  | hb p r =>
    simp only [tensorMul_smul_right, map_smul]
    suffices quotientTensorMap (tensorMul z (tensorBasis p)) = 0 by rw [this, smul_zero]
    apply kills_tensor_kernel (quotientTensorMap.comp (tensorMulLinear.flip (tensorBasis p))) ?_ ?_ hz
    · intro a ha b
      change quotientTensorMap (tensorMul (a ⊗ₜ[ℤ] b) (tensorBasis p)) = 0
      rw [tensorMul_tmul_basis, quotientTensorMap_tmul,
        (pi_eq_zero_iff _).mpr (radical_mul_right ha _), TensorProduct.zero_tmul]
    · intro b hb a
      change quotientTensorMap (tensorMul (a ⊗ₜ[ℤ] b) (tensorBasis p)) = 0
      rw [tensorMul_tmul_basis, quotientTensorMap_tmul,
        (pi_eq_zero_iff _).mpr (radical_mul_right (twist_radical _ hb) _), TensorProduct.tmul_zero]

theorem quotientTensorMap_surjective : Function.Surjective quotientTensorMap := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul x y =>
    obtain ⟨a, rfl⟩ := pi_surjective x
    obtain ⟨b, rfl⟩ := pi_surjective y
    exact ⟨a ⊗ₜ[ℤ] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a+b, map_add _ _ _⟩

/-- Linear descent along precisely the actual quotient tensor map. -/
def descendTensor {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : T →ₗ[ℤ] M) (hf : ∀ z, quotientTensorMap z = 0 → f z = 0) :
    (Q ⊗[ℤ] Q) →ₗ[ℤ] M :=
  ((LinearMap.ker quotientTensorMap).liftQ f hf).comp
    (quotientTensorMap.quotKerEquivOfSurjective quotientTensorMap_surjective).symm.toLinearMap

@[simp] theorem descendTensor_map {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : T →ₗ[ℤ] M) (hf : ∀ z, quotientTensorMap z = 0 → f z = 0) (z : T) :
    descendTensor f hf (quotientTensorMap z) = f z := by
  let e := quotientTensorMap.quotKerEquivOfSurjective quotientTensorMap_surjective
  change (LinearMap.ker quotientTensorMap).liftQ f hf (e.symm (quotientTensorMap z)) = _
  have he : e (Submodule.Quotient.mk z) = quotientTensorMap z := rfl
  rw [← he, e.symm_apply_apply]
  rfl

private def mulRight (x : T) : (Q ⊗[ℤ] Q) →ₗ[ℤ] Q ⊗[ℤ] Q :=
  descendTensor (quotientTensorMap.comp (tensorMulLinear x))
    (fun _ hz => tensor_kernel_mul_right x hz)

private theorem mulRight_map (x y : T) :
    mulRight x (quotientTensorMap y) = quotientTensorMap (tensorMul x y) :=
  descendTensor_map _ _ _

private def mulToQuotient : T →ₗ[ℤ] (Q ⊗[ℤ] Q) →ₗ[ℤ] Q ⊗[ℤ] Q where
  toFun := mulRight
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := quotientTensorMap_surjective z
    simp only [LinearMap.add_apply, mulRight_map, tensorMul_add_left, map_add]
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := quotientTensorMap_surjective z
    simp only [LinearMap.smul_apply, mulRight_map, tensorMul_smul_left, map_smul,
      RingHom.id_apply]

/-- Signed, bilinear tensor multiplication on the exact EK radical quotient. -/
def quotientTensorMul : (Q ⊗[ℤ] Q) →ₗ[ℤ] (Q ⊗[ℤ] Q) →ₗ[ℤ] Q ⊗[ℤ] Q :=
  descendTensor mulToQuotient (by
    intro x hx
    apply LinearMap.ext
    intro y
    obtain ⟨y, rfl⟩ := quotientTensorMap_surjective y
    change mulRight x (quotientTensorMap y) = 0
    rw [mulRight_map]
    exact tensor_kernel_mul_left hx y)

/-- Complete well-definedness/descent law, for arbitrary free tensors. -/
@[simp] theorem quotientTensorMul_map (x y : T) :
    quotientTensorMul (quotientTensorMap x) (quotientTensorMap y) =
      quotientTensorMap (tensorMul x y) := by
  unfold quotientTensorMul
  rw [descendTensor_map]
  exact mulRight_map x y

theorem quotientTensorMul_assoc (x y z : Q ⊗[ℤ] Q) :
    quotientTensorMul (quotientTensorMul x y) z =
      quotientTensorMul x (quotientTensorMul y z) := by
  obtain ⟨x, rfl⟩ := quotientTensorMap_surjective x
  obtain ⟨y, rfl⟩ := quotientTensorMap_surjective y
  obtain ⟨z, rfl⟩ := quotientTensorMap_surjective z
  simp only [quotientTensorMul_map, tensorMul_assoc]

@[simp] theorem quotientTensorMap_one :
    quotientTensorMap tensorOne = ((1 : Q) ⊗ₜ[ℤ] (1 : Q)) := by
  simp [tensorOne]

@[simp] theorem quotientTensorMul_one_left (x : Q ⊗[ℤ] Q) :
    quotientTensorMul ((1 : Q) ⊗ₜ[ℤ] (1 : Q)) x = x := by
  obtain ⟨x, rfl⟩ := quotientTensorMap_surjective x
  rw [← quotientTensorMap_one, quotientTensorMul_map, tensorMul_one_left]

@[simp] theorem quotientTensorMul_one_right (x : Q ⊗[ℤ] Q) :
    quotientTensorMul x ((1 : Q) ⊗ₜ[ℤ] (1 : Q)) = x := by
  obtain ⟨x, rfl⟩ := quotientTensorMap_surjective x
  rw [← quotientTensorMap_one, quotientTensorMul_map, tensorMul_one_right]

/-- Cor.2.4 signed compatibility for the already constructed genuine coproduct. -/
theorem quotient_coproduct_mul (x y : Q) :
    quotientCoproduct (x*y) = quotientTensorMul (quotientCoproduct x) (quotientCoproduct y) := by
  obtain ⟨x, rfl⟩ := pi_surjective x
  obtain ⟨y, rfl⟩ := pi_surjective y
  rw [← pi.map_mul, quotientCoproduct_pi, coproduct_mul, quotientCoproduct_pi,
    quotientCoproduct_pi, quotientTensorMul_map]

@[simp] theorem quotient_coproduct_one :
    quotientCoproduct (1 : Q) = (1 : Q) ⊗ₜ[ℤ] (1 : Q) := by
  calc
    quotientCoproduct 1 = quotientCoproduct (pi 1) := congrArg quotientCoproduct pi.map_one.symm
    _ = _ := by rw [quotientCoproduct_pi, coproduct_one, quotientTensorMap_one]

@[simp] theorem quotient_counit_mul (x y : Q) :
    quotientCounit (x*y) = quotientCounit x * quotientCounit y := quotientCounit.map_mul x y

@[simp] theorem quotient_counit_one : quotientCounit (1 : Q) = 1 := quotientCounit.map_one

/-- The literal source Koszul sign on arbitrary word images, including zero parts. -/
theorem quotientTensorMul_hWords (α β γ δ : List ℕ) :
    quotientTensorMul (pi (hWord α) ⊗ₜ[ℤ] pi (hWord β))
      (pi (hWord γ) ⊗ₜ[ℤ] pi (hWord δ)) =
      (-1 : ℤ)^(β.sum * γ.sum) •
        ((pi (hWord α) * pi (hWord γ)) ⊗ₜ[ℤ] (pi (hWord β) * pi (hWord δ))) := by
  rw [← quotientTensorMap_tmul, ← quotientTensorMap_tmul, quotientTensorMul_map,
    tensorMul_hWords, map_smul, quotientTensorMap_tmul, pi.map_mul, pi.map_mul]

end OddMath.Frontier.EKSignedQuotient
