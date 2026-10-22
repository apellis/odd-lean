import OddMath

/-! # Serre ideal equals the radical for an infinite index set

The super Cartan datum on `ℕ` with `aᵢⱼ = 2δᵢⱼ`, `dᵢ = 1` and every simple root odd (an infinite
product of copies of `𝔬𝔰𝔭(1|2)`); it is bar-consistent. The generic covering form radical is the
Serre ideal (`Coefficients.serreIdeal_eq_radical`, no finiteness of the index set), so the form
on the Serre presentation is nondegenerate.
-/

noncomputable section
open OddMath OddMath.CoveringQuantum

namespace NonVacuity.SerreRestrict

/-- The datum `aᵢⱼ = 2δᵢⱼ`, `dᵢ = 1`, all simple roots odd, on `ℕ`. -/
def cartan : SuperCartanDatum ℕ where
  a := Matrix.of fun i j ↦ if i = j then 2 else 0
  isGCM :=
    { diag := fun _ ↦ by simp
      offDiag_nonpos := fun i j h ↦ by simp [h]
      zero_comm := fun i j ↦ by simp [eq_comm] }
  d := fun _ ↦ 1
  d_pos := fun _ ↦ one_pos
  d_mul_symm := fun i j ↦ by by_cases h : i = j <;> simp [h, eq_comm]
  parity := fun _ ↦ 1
  even_of_odd := fun i j _ ↦ by by_cases h : i = j <;> simp [h]

theorem barConsistent : cartan.BarConsistent := fun _ ↦ Nat.cast_one

example : cartan.serreIdeal Coefficients.q Coefficients.pi =
    PreF.radical (cartan.chi Coefficients.q Coefficients.pi)
      (cartan.norm Coefficients.q Coefficients.pi) :=
  Coefficients.serreIdeal_eq_radical cartan barConsistent

example : (cartan.serreForm Coefficients.q Coefficients.pi Coefficients.pi_sq).Nondegenerate :=
  Coefficients.serreForm_nondegenerate cartan barConsistent

end NonVacuity.SerreRestrict
