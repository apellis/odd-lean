import OddMath.Frontier.EKDeterminant

/-! Test-first controls for the corrected EK1107.5610v2 (3.4), compiled before
`EKDeterminantCorrected` exists.

* The exponent of the corrected sign is `(#index − #fixed points)/2`, the
  number of 2-cycles of an involution. The toy permutations below separate this
  from the tempting but wrong `(−1)^(#index − #fixed)` and `(−1)^#fixed`.
* Degree two: two shapes, none self-transpose, so the corrected factor
  `(−1)^((2−0)/2) = −1` must reproduce the kernel-checked `det M₂ = −1`. -/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKDeterminantCorrectedControls
open DegreeShapes EKDualBases EKDeterminant EKDeterminantControls EKDualBasesControls
local instance : DecidableEq YoungDiagram := Classical.decEq _
local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-- One transposition, one fixed point: (3−1)/2 = 1 two-cycle, sign −1. -/
theorem toy_one_fixed :
    Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = -1 ∧
    (Finset.univ.filter (fun x : Fin 3 => Equiv.swap (0 : Fin 3) 1 x = x)).card = 1 := by
  decide

/-- Two disjoint transpositions, no fixed points: (4−0)/2 = 2, sign +1,
although #index − #fixed = 4 and #fixed = 0 give the same parity here;
the next control separates the halving. -/
theorem toy_two_cycles :
    Equiv.Perm.sign (Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) = 1 ∧
    (Finset.univ.filter
      (fun x : Fin 4 => (Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3) x = x)).card = 0 := by
  decide

/-- One transposition, no fixed point: #index − #fixed = 2 is even, but the
sign is −1, so the halving in the exponent is essential. -/
theorem toy_halving :
    Equiv.Perm.sign (Equiv.swap (0 : Fin 2) 1) = -1 ∧
    (Finset.univ.filter (fun x : Fin 2 => Equiv.swap (0 : Fin 2) 1 x = x)).card = 0 := by
  decide

/-- Exhaustive degree-two index has exactly two shapes. -/
theorem degree_two_card : Fintype.card (DegreeShape 2) = 2 := by
  rw [← Fintype.card_fin 2]
  exact (Fintype.card_congr degreeTwoEquiv).symm

/-- No self-transpose shape in degree two (count form). -/
theorem degree_two_sc :
    (Finset.univ.filter (fun μ : DegreeShape 2 => μ.val.transpose = μ.val)).card = 0 := by
  rw [degree_two_filter, Finset.card_empty]

/-- Target value the corrected formula must reproduce in degree two. -/
theorem degree_two_target :
    (-1 : ℤ)^((2 - 0)/2) * sourceRHS 2 = (M 2).det := by
  rw [degree_two_rhs, degree_two_det]
  norm_num

end OddMath.Frontier.EKDeterminantCorrectedControls
