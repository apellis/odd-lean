import OddMath.QuiverHecke.CyclotomicAction.BoundaryDivision

/-! Non-vacuity checks in `NonVacuity.BoundaryDivision`.
Conventions are in `scripts/NonVacuity.lean`. -/

noncomputable section

namespace NonVacuity.BoundaryDivision
open OddMath.QuiverHecke.CyclotomicAction.BoundaryPolynomial

/-- `φ_k = t^k` over `ℚ` with `σ = id`, `S = t` (monic of degree `1`), `F = t`. -/
abbrev φ (k : ℕ) : ℕ →₀ ℚ := Finsupp.single k 1

theorem tShift_single (k : ℕ) : tShift (RingHom.id ℚ) (φ k) = φ (k + 1) := by
  ext l
  rcases l with _ | l
  · simp
  · rw [tShift_succ]; simp [Finsupp.single_apply]

theorem tPow_single (j k : ℕ) : tPow (RingHom.id ℚ) j (φ k) = φ (k + j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [tPow_succ, ih, tShift_single, add_assoc]

theorem recurrence (k : ℕ) :
    DegLT (φ (k + 1) - tShift (RingHom.id ℚ) (φ k)) 1 := by
  rw [tShift_single, sub_self]
  exact DegLT.zero 1

theorem monic_t : MonicDeg (φ 1) 1 :=
  ⟨by simp, fun l hl => by simp [Finsupp.single_apply]; omega⟩

theorem norm (k : ℕ) : ∑ j ∈ Finset.range (1 + 1), rsmul (φ 1 j) (φ (k + j)) =
    lsmul ((1 : ℚˣ) : ℚ) (tPow (RingHom.id ℚ) k (φ 1)) := by
  rw [tPow_single]
  ext l
  simp [Finset.sum_range_succ, add_comm]

/-- Both branches of the division conclusion occur: `φ_0 = 1` is monic of degree `0` and
`φ_3 = t^3` is monic of degree `3`. -/
example : MonicDeg (lsmul (↑(1 : ℚˣ)⁻¹ : ℚ) (φ 3)) 3 :=
  (boundary_division (RingHom.id ℚ) Function.injective_id φ recurrence monic_t monic_t 1
    (map_one _) norm 3).2 (by omega)

example : MonicDeg (lsmul (↑(1 : ℚˣ)⁻¹ : ℚ) (φ 0)) 0 :=
  (boundary_division (RingHom.id ℚ) Function.injective_id φ recurrence monic_t monic_t 1
    (map_one _) norm 0).2 (by omega)

end NonVacuity.BoundaryDivision
