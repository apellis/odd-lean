/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.CoveringQuantum.UDot.SkewNilpotence
import OddMath.CoveringQuantum.UDot.LoweringNilpotence
import OddMath.CoveringQuantum.UDot.NativeCyclic.RaisingNilpotence

/-!
Local nilpotence of the original mixed tensor Chevalley operators. The toral,
Koszul and original Clark-omega factors are retained, for both coproducts.
This does not identify printed tau1/Delta3/Delta4 or prove form nondegeneracy.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open PreF Coefficients TensorProduct TensorNilpotence
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
variable (D : RootDatum I X) (Λ Μ : X)

local instance : AddCommGroup
    (IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ) :=
  TensorProduct.addCommGroup

omit [DecidableEq I] [DecidableEq X] in
private theorem chi_inverse (i : I) :
    D.chi Coefficients.q⁻¹ pi i i * D.chi Coefficients.q pi i i = 1 := by
  simp only [SuperCartanDatum.chi_apply, inv_zpow, ← zpow_neg, neg_neg]
  have hp : pi ^ (D.parity i * D.parity i).val * pi ^ (D.parity i * D.parity i).val = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm _ 2, pow_mul, pi_sq, one_pow]
  calc
    _ = ((Coefficients.q ^ D.dot i i : Coefficients.Ringˣ) : Coefficients.Ring) *
        ((Coefficients.q ^ (-D.dot i i) : Coefficients.Ringˣ) : Coefficients.Ring) *
        (pi ^ (D.parity i * D.parity i).val * pi ^ (D.parity i * D.parity i).val) := by ring
    _ = 1 := by rw [hp, ← Units.val_mul, ← zpow_add]; simp

/-- The actual two summands of tensorE scalar-commute, including its toral and
Koszul factors. This is an equality on the entire tensor. -/
theorem tensorE_summands_skew (withJ : Bool) (i : I) :
    TensorProduct.map (tensorTwist D Λ withJ i) (integrableChevalley D Μ false i) *
        TensorProduct.map (integrableChevalley D Λ true i) LinearMap.id =
      D.chi Coefficients.q pi i i •
        (TensorProduct.map (integrableChevalley D Λ true i) LinearMap.id *
          TensorProduct.map (tensorTwist D Λ withJ i) (integrableChevalley D Μ false i)) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, Module.End.mul_apply,
    LinearMap.smul_apply, map_tmul, LinearMap.id_apply, tensorTwist_E,
    smul_tmul, tmul_smul]

/-- Arbitrary vectors of the original mixed tensor are killed by a power of the
original tensorE, for both Delta1 and Delta2, at arbitrary highest weights. -/
theorem tensorE_locally_nilpotent
    (z : IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ)
    (withJ : Bool) (i : I) : ∃ n : ℕ, (tensorE D Λ Μ withJ i ^ n) z = 0 := by
  let A := TensorProduct.map (integrableChevalley D Λ true i)
    (LinearMap.id : Module.End Coefficients.Ring (IntegrableQuotient D Μ))
  let B := TensorProduct.map (tensorTwist D Λ withJ i) (integrableChevalley D Μ false i)
  have hba : B * A = D.chi Coefficients.q pi i i • (A * B) :=
    tensorE_summands_skew D Λ Μ withJ i
  have hab : A * B = D.chi Coefficients.q⁻¹ pi i i • (B * A) := by
    rw [hba, smul_smul, chi_inverse, one_smul]
  exact skew_sum_locally_nilpotent A B _ _ hab hba
    (map_left_locally_nilpotent _ _
      (fun x ↦ NativeLeading.integrableChevalley_true_locally_nilpotent D Λ x i))
    (map_right_locally_nilpotent _ _
      (fun y ↦ integrableChevalley_false_locally_nilpotent D Μ y i)) z

/-- Local nilpotence of the original omega-lowest F, with its pi-sign retained. -/
theorem lowestF_locally_nilpotent (y : IntegrableQuotient D Μ) (i : I) :
    ∃ n : ℕ, (lowestF D Μ i ^ n) y = 0 := by
  obtain ⟨n, hn⟩ := NativeLeading.integrableChevalley_true_locally_nilpotent D Μ y i
  refine ⟨n, ?_⟩
  rw [lowestF_eq_smul, smul_pow, LinearMap.smul_apply, hn, smul_zero]

/-- The actual F summands scalar-commute. The K on the second factor and the
omega-lowest F are not replaced by a simplified action. -/
theorem tensorF_summands_skew (withJ : Bool) (i : I) :
    TensorProduct.map (integrableChevalley D Λ false i) (tensorK D Μ i) *
        TensorProduct.map (tensorFTwist D Λ withJ i) (lowestF D Μ i) =
      D.chi Coefficients.q pi i i •
        (TensorProduct.map (tensorFTwist D Λ withJ i) (lowestF D Μ i) *
          TensorProduct.map (integrableChevalley D Λ false i) (tensorK D Μ i)) := by
  have hs : pi ^ (D.parity i * D.parity i).val * pi ^ (D.parity i * D.parity i).val = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm _ 2, pow_mul, pi_sq, one_pow]
  have hp : integrableChevalley D Λ false i * tensorFTwist D Λ withJ i =
      pi ^ (D.parity i * D.parity i).val •
        (tensorFTwist D Λ withJ i * integrableChevalley D Λ false i) := by
    rw [tensorFTwist_chevalley, smul_smul, hs, one_smul]
  simp only [← TensorProduct.map_mul, lowestF_eq_smul,
    mul_smul_comm, smul_mul_assoc, tensorK_E, hp]
  simp only [TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul,
    SuperCartanDatum.chi_apply, qp]
  congr 1
  ring

/-- Arbitrary vectors of the original mixed tensor are killed by a power of the
original tensorF, for both Delta1 and Delta2, at arbitrary highest weights. -/
theorem tensorF_locally_nilpotent
    (z : IntegrableQuotient D Λ ⊗[Coefficients.Ring] IntegrableQuotient D Μ)
    (withJ : Bool) (i : I) : ∃ n : ℕ, (tensorF D Λ Μ withJ i ^ n) z = 0 := by
  let A := TensorProduct.map (integrableChevalley D Λ false i) (tensorK D Μ i)
  let B := TensorProduct.map (tensorFTwist D Λ withJ i) (lowestF D Μ i)
  have hab : A * B = D.chi Coefficients.q pi i i • (B * A) :=
    tensorF_summands_skew D Λ Μ withJ i
  have hba : B * A = D.chi Coefficients.q⁻¹ pi i i • (A * B) := by
    rw [hab, smul_smul, chi_inverse, one_smul]
  exact skew_sum_locally_nilpotent A B _ _ hab hba
    (map_left_locally_nilpotent _ _
      (fun x ↦ integrableChevalley_false_locally_nilpotent D Λ x i))
    (map_right_locally_nilpotent _ _
      (fun y ↦ lowestF_locally_nilpotent D Μ y i)) z

end OddMath.CoveringQuantum.UDot.GenericVerma
