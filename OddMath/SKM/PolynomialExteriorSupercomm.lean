import OddMath.SKM.BubbleParity
import OddMath.SKM.Calculus
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-! # Supercommutativity of the full polynomial/exterior coefficient model

Homogeneous coefficients supercommute with their actual exterior parity. This
uses the exterior algebra itself, so retains all odd coefficient generators.
-/
noncomputable section
open scoped Classical TensorProduct
namespace OddMath.SKM.SYM
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X)

private theorem signed_units_pow_smul (n : ℕ) (x : ExteriorAlgebra k (OddModule D k)) :
    ((-1 : ℤˣ) ^ n) • x = zsign k (n : ZMod 2) • x := by
  induction n with
  | zero => simp [zsign]
  | succ n ih =>
    rw [pow_succ, mul_smul, Units.neg_smul, one_smul, smul_neg, ih]
    simp only [Nat.cast_add, Nat.cast_one, zsign_add, show zsign k 1 = -1 from rfl,
      mul_smul, neg_one_smul, smul_neg]

private theorem exterior_power_supercomm {m n : ℕ}
    {a b : ExteriorAlgebra k (OddModule D k)}
    (ha : a ∈ ExteriorAlgebra.exteriorPower k m (OddModule D k))
    (hb : b ∈ ExteriorAlgebra.exteriorPower k n (OddModule D k)) :
    a * b = zsign k ((m : ZMod 2) * (n : ZMod 2)) • (b * a) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at ha hb
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      rw [ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm, signed_units_pow_smul]
      simp only [Nat.cast_mul, mul_comm]
    | zero => simp
    | add y z _ _ hy hz => simp only [mul_add, add_mul, hy, hz, smul_add]
    | smul c y _ hy => simp only [mul_smul_comm, smul_mul_assoc, hy, smul_comm c]
  | zero => simp
  | add x y _ _ hx hy => simp only [mul_add, add_mul, hx, hy, smul_add]
  | smul c x _ hx => simp only [mul_smul_comm, smul_mul_assoc, hx, smul_comm c]

/-- The actual exterior parity pieces satisfy the Koszul commutation rule. -/
theorem exteriorParity_supercomm {p q : ZMod 2}
    {a b : ExteriorAlgebra k (OddModule D k)}
    (ha : a ∈ exteriorParity D k p) (hb : b ∈ exteriorParity D k q) :
    a * b = zsign k (p * q) • (b * a) := by
  change a ∈ ⨆ n : {n : ℕ // (n : ZMod 2) = p},
    ExteriorAlgebra.exteriorPower k n.1 (OddModule D k) at ha
  change b ∈ ⨆ n : {n : ℕ // (n : ZMod 2) = q},
    ExteriorAlgebra.exteriorPower k n.1 (OddModule D k) at hb
  induction ha using Submodule.iSup_induction' with
  | mem i a ha =>
    induction hb using Submodule.iSup_induction' with
    | mem j b hb => simpa only [i.property, j.property] using exterior_power_supercomm D ha hb
    | zero => simp
    | add x y _ _ hx hy => simp only [mul_add, add_mul, hx, hy, smul_add]
  | zero => simp
  | add x y _ _ hx hy => simp only [mul_add, add_mul, hx, hy, smul_add]

/-- Supercommutativity of the full polynomial/exterior coefficient algebra. -/
theorem polynomialExteriorParity_supercomm {p q : ZMod 2}
    {a b : PolynomialExterior D k}
    (ha : a ∈ polynomialExteriorParity D k p)
    (hb : b ∈ polynomialExteriorParity D k q) :
    a * b = zsign k (p * q) • (b * a) := by
  change a ∈ (exteriorParity D k p).baseChange (MvPolynomial (I × ℕ) k) at ha
  change b ∈ (exteriorParity D k q).baseChange (MvPolynomial (I × ℕ) k) at hb
  rw [Submodule.baseChange_eq_span] at ha hb
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      change (1 ⊗ₜ[k] v) * (1 ⊗ₜ[k] w) =
        zsign k (p * q) • ((1 ⊗ₜ[k] w) * (1 ⊗ₜ[k] v))
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        exteriorParity_supercomm D hv hw, TensorProduct.tmul_smul]
    | zero => simp
    | add y z _ _ hy hz => simp only [mul_add, add_mul, hy, hz, smul_add]
    | smul c y _ hy => simp only [mul_smul_comm, smul_mul_assoc, hy, smul_comm c]
  | zero => simp
  | add x y _ _ hx hy => simp only [mul_add, add_mul, hx, hy, smul_add]
  | smul c x _ hx => simp only [mul_smul_comm, smul_mul_assoc, hx, smul_comm c]

end OddMath.SKM.SYM
