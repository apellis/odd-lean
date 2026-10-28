import OddMath.SKM.RouquierHomMixedRational
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-! Nonempty odd block matrices over Z/9, where 2 is invertible but the
coefficient ring is not a domain. The block grading is 3|3; both dots have
zero diagonal blocks. The reservoir cube vanishes but its square does not. -/
open OddMath.SKM Matrix
open scoped BigOperators
namespace NonVacuity.RouquierHomMixedRational
abbrev K := ZMod 9
abbrev A := Matrix (Fin 3) (Fin 3) K
abbrev S := Matrix (Fin 2) (Fin 2) A

def shift : A := !![0,1,0; 0,0,1; 0,0,0]
def probe : S := !![0,1; 1,0]
def reservoir : S := !![0,shift; -shift,0]

lemma shift_cube : shift ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

lemma probe_square : probe * probe = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [probe, Matrix.mul_apply, Fin.sum_univ_two]

def probeUnit : Sˣ := ⟨probe, probe, probe_square, probe_square⟩

lemma exchange : probe * reservoir = -(reservoir * probe) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [probe, reservoir, Matrix.mul_apply, Fin.sum_univ_two]

lemma reservoir_cube : reservoir ^ 3 = 0 := by
  ext i j a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;> decide

lemma reservoir_square_ne : reservoir ^ 2 ≠ 0 := by
  intro h
  have ht := congrArg (fun m : S => m 0 0 0 2) h
  revert ht
  decide

example : reservoir ≠ 0 := by
  intro h
  apply reservoir_square_ne
  simp [h]

example : (2 : K) * 5 = 1 := by decide
example : (3 : K) ≠ 0 ∧ (3 : K) * 3 = 0 := by decide

/-- Both dots are odd for the displayed block grading. -/
example (i : Fin 2) : probe i i = 0 ∧ reservoir i i = 0 := by
  fin_cases i <;> simp [probe, reservoir]

example : IsUnit (probe ^ 2 - reservoir ^ 2) :=
  mixedOddDenominator_isUnit probeUnit reservoir exchange 3 reservoir_cube

example : (probe ^ 2 - reservoir ^ 2) * Ring.inverse (probe ^ 2 - reservoir ^ 2) = 1 ∧
    Ring.inverse (probe ^ 2 - reservoir ^ 2) * (probe ^ 2 - reservoir ^ 2) = 1 := by
  have hu := mixedOddDenominator_isUnit probeUnit reservoir exchange 3 reservoir_cube
  exact ⟨Ring.mul_inverse_cancel _ hu, Ring.inverse_mul_cancel _ hu⟩

example : (probe - reservoir) * Ring.inverse (probe ^ 2 - reservoir ^ 2) =
    ∑ r ∈ Finset.range 6, (-1 : S) ^ r * probe ^ (r + 1) * reservoir ^ r :=
  mixedOddInverse_expansion probeUnit reservoir exchange 3 reservoir_cube

/-- The even specialization exercises the same nonzero nilpotent reservoir. -/
example : Ring.inverse ((1 : S) - reservoir) =
    ∑ r ∈ Finset.range 3, reservoir ^ r := by
  simpa using mixedEvenInverse_expansion (1 : Sˣ) reservoir (Commute.one_left _) 3 reservoir_cube

/-- The unsigned expansion is not the prescribed odd coefficient. -/
example : (∑ r ∈ Finset.range 6, (-1 : S) ^ r * probe ^ (r + 1) * reservoir ^ r) ≠
    (∑ r ∈ Finset.range 6, probe ^ (r + 1) * reservoir ^ r) := by
  intro h
  have ht := congrArg (fun m : S => m 0 1 0 1) h
  revert ht
  decide

#print axioms mixedEvenDenominator_isUnit
#print axioms mixedEvenInverse_expansion
#print axioms mixedOddDenominator_isUnit
#print axioms mixedOddInverse_expansion
#print axioms homContentMixedRational_even
#print axioms homContentMixedRational_odd
end NonVacuity.RouquierHomMixedRational
