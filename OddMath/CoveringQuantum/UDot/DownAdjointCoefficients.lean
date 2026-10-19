import OddMath.CoveringQuantum.UDot.AdjointCoefficients

/-!
# Downward adjoint Laurent coefficients

BE2, arXiv:1701.04133v2, Theorem 10.3 Claim 3, algebraic step only.
The star formula (9.9), not rho alone, supplies the parity factor.
Finite colours and bar consistency remain explicit route hypotheses.
-/
noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericTensor
open Coefficients
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X]
  [Finite I] (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent)

/-- The downward adjoint for arbitrary modified inputs. F has right weight ν;
its adjoint E has right weight ν − αᵢ. The π factor is the original star's. -/
theorem sesquilinearForm_F_adjoint (i : I) (ν : X)
    (x y : modified D Coefficients.q pi) :
    sesquilinearForm D hD
      (⟨F D Coefficients.q pi i ν, F_mem_modified D Coefficients.q pi i ν⟩ * x) y =
    (qp Coefficients.q (D.d i * (D.h i ν - 1)) * pi ^ (D.parl i ν).val) *
      sesquilinearForm D hD x
        (⟨E D Coefficients.q pi i (ν - D.α i),
          E_mem_modified D Coefficients.q pi i (ν - D.α i)⟩ * y) := by
  rw [sesquilinearForm_adjoint]
  have hs : starModified D
      ⟨F D Coefficients.q pi i ν, F_mem_modified D Coefficients.q pi i ν⟩ =
      (qp Coefficients.q (D.d i * (D.h i ν - 1)) * pi ^ (D.parl i ν).val) •
        (⟨E D Coefficients.q pi i (ν - D.α i),
          E_mem_modified D Coefficients.q pi i (ν - D.α i)⟩ :
          modified D Coefficients.q pi) :=
    Subtype.ext (star_F (D := D) barData i ν)
  rw [hs, smul_mul_assoc, map_smul, smul_eq_mul]

/-- Bending a downward generator contributes q^{dᵢ(1−hᵢν)}π^{|i,ν|}.
In particular its parity factor cannot be dropped by analogy with E. -/
theorem sesquilinearForm_F_bent (i : I) (ν : X)
    (x y : modified D Coefficients.q pi) :
    sesquilinearForm D hD x
      (⟨E D Coefficients.q pi i (ν - D.α i),
        E_mem_modified D Coefficients.q pi i (ν - D.α i)⟩ * y) =
    (qp Coefficients.q (D.d i * (1 - D.h i ν)) * pi ^ (D.parl i ν).val) *
      sesquilinearForm D hD
        (⟨F D Coefficients.q pi i ν, F_mem_modified D Coefficients.q pi i ν⟩ * x) y := by
  rw [sesquilinearForm_F_adjoint]
  have hq : qp Coefficients.q (D.d i * (1 - D.h i ν)) *
      qp Coefficients.q (D.d i * (D.h i ν - 1)) = 1 := by
    rw [qp_mul, show D.d i * (1 - D.h i ν) + D.d i * (D.h i ν - 1) = 0 by ring,
      qp_zero]
  have hp : pi ^ (D.parl i ν).val * pi ^ (D.parl i ν).val = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, pi_sq, one_pow]
  symm
  calc
    _ = (qp Coefficients.q (D.d i * (1 - D.h i ν)) *
          qp Coefficients.q (D.d i * (D.h i ν - 1))) *
        (pi ^ (D.parl i ν).val * pi ^ (D.parl i ν).val) *
        sesquilinearForm D hD x
          (⟨E D Coefficients.q pi i (ν - D.α i),
            E_mem_modified D Coefficients.q pi i (ν - D.α i)⟩ * y) := by ring
    _ = _ := by rw [hq, hp, one_mul, one_mul]

/-- BE2 Theorem 10.3 Claim 3: the formal Laurent coefficient step.
Only π is specialized, after evaluating the original modified form.
No graphical comparison or mixed-word reversal is assumed. -/
theorem sesquilinearForm_F_bent_coeff (σ : ℚ) (hσ : σ ^ 2 = 1)
    (i : I) (ν : X) (x y : modified D Coefficients.q pi) (z : ℤ) :
    (signLaurent σ hσ (sesquilinearForm D hD x
      (⟨E D Coefficients.q pi i (ν - D.α i),
        E_mem_modified D Coefficients.q pi i (ν - D.α i)⟩ * y))).coeff z =
    σ ^ (D.parl i ν).val *
      (signLaurent σ hσ (sesquilinearForm D hD
        (⟨F D Coefficients.q pi i ν, F_mem_modified D Coefficients.q pi i ν⟩ * x) y)).coeff
          (z - D.d i * (1 - D.h i ν)) := by
  rw [sesquilinearForm_F_bent, map_mul, map_mul, map_pow, signLaurent_qp,
    signLaurent_pi, ← map_pow]
  rw [mul_assoc, HahnSeries.coeff_single_mul, one_mul, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_smul, smul_eq_mul]

end OddMath.CoveringQuantum.UDot.GenericTensor
