import OddMath.Frontier.EQOnhDG
import DG.Bigraded.Basic

/-!
# `ONH_{n+2}` as a dg ring

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§2.2, §3.2 (Proposition 3.3) and Proposition 3.16(2). Conventions as in
`OddMath.Frontier.EQOnhDG`: the `ℤ`-grading is half the `q`-degree (`x_i` in degree `1`, `∂_i`
in degree `-1`).
-/

noncomputable section

namespace OddMath.Frontier.EQOnhDG

open CategoryTheory StringDiagrams
open OddMath.Diagrams.OddNilHecke
open OddMath.Frontier NilHeckeAction
open DirectSum

theorem x_mem_endDeg_zDeg (n i : ℕ) : x ℤ n i ∈ (pres ℤ).endDeg zDeg (strands n) 1 := by
  by_cases h : i < n
  · rw [x_def ℤ h]
    exact Presentation.diag_mem_homDeg' (degree_dlay_zDeg _)
  · rw [x, dite_eq_right h]; exact Submodule.zero_mem _

theorem ψ_mem_endDeg_zDeg (n i : ℕ) : ψ ℤ n i ∈ (pres ℤ).endDeg zDeg (strands n) (-1) := by
  by_cases h : i + 1 < n
  · rw [ψ_def ℤ h]
    exact Presentation.diag_mem_homDeg' (degree_dlay_zDeg _)
  · rw [ψ, dite_eq_right h]; exact Submodule.zero_mem _

/-! ## The grading of `Presented n` -/

/-- The degree-`k` part of the endomorphism ring of `n + 2` strands, as an additive subgroup. -/
abbrev endGrading (n : ℕ) (k : ℤ) : AddSubgroup (End ((pres ℤ).obj (strands (n + 2)))) :=
  ((pres ℤ).endDeg zDeg (strands (n + 2)) k).toAddSubgroup

/-- The decomposition of the endomorphism ring of `n + 2` strands by `ℤ`-degree. -/
@[instance_reducible]
def endDecomposition (n : ℕ) : Decomposition (endGrading n) :=
  let D := Presentation.decomposition isHomogeneous_zDeg (strands (n + 2)) (strands (n + 2))
  { decompose' := D.decompose'
    left_inv := D.left_inv
    right_inv := D.right_inv }

/-- The degree-`k` part of `ONH_{n+2}` (half the Ellis–Qi `q`-degree). -/
def grading (n : ℕ) (k : ℤ) : AddSubgroup (Presented n) :=
  (endGrading n k).comap (presentedEquivEnd n).toAddMonoidHom

theorem mem_grading {n : ℕ} {k : ℤ} {p : Presented n} :
    p ∈ grading n k ↔ presentedEquivEnd n p ∈ (pres ℤ).endDeg zDeg (strands (n + 2)) k :=
  Iff.rfl

/-- `Presented n` is the internal direct sum of its homogeneous parts. -/
theorem isInternal_grading (n : ℕ) : IsInternal (grading n) :=
  letI := endDecomposition n
  DG.isInternal_comap (endGrading n) (presentedEquivEnd n).toAddMonoidHom
    (presentedEquivEnd n).injective
    fun _ _ => (presentedEquivEnd n).surjective _ |>.imp fun _ h => h

/-- The decomposition of `ONH_{n+2}` by `ℤ`-degree. -/
@[instance_reducible]
def decomposition (n : ℕ) : Decomposition (grading n) := (isInternal_grading n).chooseDecomposition

theorem dot_mem_grading (n : ℕ) (j : Fin (n + 2)) : dot n j ∈ grading n 1 := by
  rw [mem_grading, presentedEquivEnd_dot]; exact x_mem_endDeg_zDeg _ _

theorem crossing_mem_grading (n : ℕ) (i : Fin (n + 1)) : crossing n i ∈ grading n (-1) := by
  rw [mem_grading, presentedEquivEnd_crossing]; exact ψ_mem_endDeg_zDeg _ _

theorem one_mem_grading (n : ℕ) : (1 : Presented n) ∈ grading n 0 := by
  rw [mem_grading, map_one]; exact SetLike.GradedOne.one_mem

theorem mul_mem_grading {n : ℕ} {i j : ℤ} {p q : Presented n} (hp : p ∈ grading n i)
    (hq : q ∈ grading n j) : p * q ∈ grading n (i + j) := by
  rw [mem_grading, map_mul]; exact SetLike.GradedMul.mul_mem hp hq

/-- **Parity is degree mod `2`**: an element of `ONH_{n+2}` of degree `k` (half its `q`-degree)
has parity `k mod 2`, for the parity grading `parity n` of Ellis–Qi §2.2. -/
theorem grading_le_parity (n : ℕ) (k : ℤ) : grading n k ≤ parity n (k : ZMod 2) :=
  fun _ hp => homDeg_zDeg_le_parityDeg _ _ k hp

/-- The differential has degree `+1`. -/
theorem dONH_mem_grading {n : ℕ} {k : ℤ} {p : Presented n} (hp : p ∈ grading n k) :
    dONH n p ∈ grading n (k + 1) := by
  rw [mem_grading, presentedEquivEnd_dONH]
  exact deriv_mem_homDeg_zDeg hp

theorem negOnePow_val_cast (k : ℤ) :
    (-1 : ℤ) ^ (k : ZMod 2).val = ((DG.koszulSign k : ℤˣ) : ℤ) := by
  rcases Int.even_or_odd k with h | h
  · rw [(ZMod.intCast_eq_zero_iff_even).mpr h, DG.koszulSign_even h]; rfl
  · rw [(ZMod.intCast_eq_one_iff_odd).mpr h, DG.koszulSign_odd h]; rfl

/-- The super Leibniz rule (Ellis–Qi (2.3)) for a left factor of degree `k`, with the Koszul sign
`(-1)^k` of the `ℤ`-grading. -/
theorem dONH_mul_of_mem {n : ℕ} {k : ℤ} {p : Presented n} (hp : p ∈ grading n k) (q : Presented n) :
    dONH n (p * q) = dONH n p * q + DG.koszulSign k • (p * dONH n q) := by
  rw [dONH_mul (grading_le_parity n k hp), Units.smul_def, zsmul_eq_mul, ← negOnePow_val_cast,
    Int.cast_pow, Int.cast_neg, Int.cast_one]

/-! ## The dg ring `ONH_{n+2}` -/

/-- The dg odd nilHecke algebra `(ONH_{n+2}, d)` of Ellis–Qi §3.2, as a dg ring: graded by half
the `q`-degree (`x_i` in degree `1`, `∂_i` in degree `-1`), with `d(x_i) = x_i²` and `d(∂_i) = 1`.
It is a type synonym of `NilHeckeAction.Presented n`. -/
def ONH (n : ℕ) : Type := Presented n

namespace ONH

variable {n : ℕ}

instance instRing : Ring (ONH n) := presentedRing n

/-- The identification of `ONH n` with odd-lean's presented odd nilHecke ring. -/
def equiv (n : ℕ) : Presented n ≃+* ONH n := RingEquiv.refl _

/-- The dot `x_{j+1}`. -/
def x (j : Fin (n + 2)) : ONH n := equiv n (dot n j)

/-- The divided difference `∂_{i+1}`. -/
def del (i : Fin (n + 1)) : ONH n := equiv n (crossing n i)

instance instDGAddCommGroup : DG.DGAddCommGroup (ONH n) where
  grading := grading n
  decomposition := decomposition n
  d := dONH n
  d_mem' hp := dONH_mem_grading hp
  d_d' := dONH_dONH n

theorem mem_grading_iff {k : ℤ} {p : ONH n} :
    p ∈ DG.grading k ↔ (equiv n).symm p ∈ grading n k := Iff.rfl

theorem equiv_mem_grading_iff {k : ℤ} {p : Presented n} :
    equiv n p ∈ DG.grading k ↔ p ∈ grading n k := Iff.rfl

theorem symm_d (p : ONH n) : (equiv n).symm (DG.d p) = dONH n ((equiv n).symm p) := rfl

theorem d_equiv (p : Presented n) : DG.d (equiv n p) = equiv n (dONH n p) := rfl

instance instDGRing : DG.DGRing (ONH n) where
  one_mem := one_mem_grading n
  mul_mem _ _ _ _ ha hb := mul_mem_grading ha hb
  d_mul' ha b := dONH_mul_of_mem ha b

/-- `ONH_{n+2}` is a dg `ℤ`-algebra. -/
theorem dgAlgebra_int : DG.DGAlgebra ℤ (ONH n) := inferInstance

theorem x_mem_grading (j : Fin (n + 2)) : x j ∈ DG.grading (M := ONH n) 1 := dot_mem_grading n j

theorem del_mem_grading (i : Fin (n + 1)) : del i ∈ DG.grading (M := ONH n) (-1) :=
  crossing_mem_grading n i

/-- **Ellis–Qi (3.1)**: `d(x_i) = x_i²`. -/
theorem d_x (j : Fin (n + 2)) : DG.d (x j) = x j * x j := by
  rw [x, d_equiv, dONH_dot, sq, map_mul]

/-- **Ellis–Qi, Proposition 3.3**: `d(∂_i) = 1`. -/
theorem d_del (i : Fin (n + 1)) : DG.d (del i) = 1 := by
  rw [del, d_equiv, dONH_crossing, map_one]

/-- The parity of a homogeneous element of degree `k` is `k mod 2`. -/
theorem mem_parity_of_mem_grading {k : ℤ} {p : ONH n} (hp : p ∈ DG.grading k) :
    (equiv n).symm p ∈ parity n (k : ZMod 2) :=
  grading_le_parity n k hp

end ONH

end OddMath.Frontier.EQOnhDG

end
