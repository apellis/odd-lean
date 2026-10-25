/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleCoefficientGenerators

/-! # Explicit odd cyclotomic deformation coefficients

This defines the algebraic coefficient family of ELV's presentation inside
abstract SYM. It does not construct a categorical action or evaluation map.
-/
noncomputable section
open scoped Classical
namespace OddMath.SKM.SYM
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
variable (D : Datum I X) (k : Type w) [CommRing k]

/-- One-based elementary coefficients, with `chi_0=1`. -/
def elvChi (i : {i : I // D.parity i = 1}) : ℕ → SYM D k
  | 0 => 1
  | r + 1 => e D k i.1 r

theorem elvChi_mem_coefficientAtLeast (i : {i : I // D.parity i = 1}) (r : ℕ) :
    elvChi D k i r ∈ CoefficientAtLeast D k (2 * r) := by
  cases r with
  | zero => exact mem_coefficientAtLeast_zero D k 1
  | succ r =>
    simpa [elvChi, elementaryWeight, i.property] using elementary_mem_coefficientAtLeast D k i.1 r

/-- `c_(2r)=chi_r`, `c_(2r+1)=delta_i chi_r`. Distinct colours use their
independent exterior generators. -/
def elvCoefficient (i : {i : I // D.parity i = 1}) (n : ℕ) : SYM D k :=
  if n % 2 = 0 then elvChi D k i (n / 2)
  else delta D k i * elvChi D k i (n / 2)

@[simp] theorem elvCoefficient_zero (i : {i : I // D.parity i = 1}) :
    elvCoefficient D k i 0 = 1 := by simp [elvCoefficient, elvChi]

theorem elvCoefficient_mem_coefficientAtLeast (i : {i : I // D.parity i = 1}) (n : ℕ) :
    elvCoefficient D k i n ∈ CoefficientAtLeast D k n := by
  unfold elvCoefficient
  split_ifs with he
  · have hn : 2 * (n / 2) = n := by omega
    simpa only [hn] using elvChi_mem_coefficientAtLeast D k i (n / 2)
  · have hn : 1 + 2 * (n / 2) = n := by omega
    simpa only [hn] using coefficientAtLeast_mul D k (delta_mem_coefficientAtLeast D k i)
      (elvChi_mem_coefficientAtLeast D k i (n / 2))

/-- Coefficients of the monic source polynomial, with coefficients placed
on the left of the odd dot. The Koszul reordering contributes `(-1)^(N*j)`;
normalizing the source leading coefficient adds `(-1)^N`. -/
def elvMonicCoefficient (i : {i : I // D.parity i = 1}) (N : ℕ) (j : Fin (N + 1)) :
    SYM D k := ((-1 : k) ^ (N * (j.val + 1))) • elvCoefficient D k i (N - j.val)

theorem elvMonicCoefficient_mem_coefficientAtLeast
    (i : {i : I // D.parity i = 1}) (N : ℕ) (j : Fin (N + 1)) :
    elvMonicCoefficient D k i N j ∈ CoefficientAtLeast D k (N - j.val) :=
  Submodule.smul_mem _ _ (elvCoefficient_mem_coefficientAtLeast D k i (N - j.val))

@[simp] theorem elvMonicCoefficient_top (i : {i : I // D.parity i = 1}) (N : ℕ) :
    elvMonicCoefficient D k i N ⟨N, Nat.lt_succ_self N⟩ = 1 := by
  simp only [elvMonicCoefficient, Nat.sub_self, elvCoefficient_zero]
  have hp : (-1 : k) ^ (N * (N + 1)) = 1 := Even.neg_one_pow (Nat.even_mul_succ_self N)
  rw [hp, one_smul]

/-- Ordinary one-based elementary coefficients for an even-coloured dot. -/
def evenCyclotomicCoefficient (i : I) : ℕ → SYM D k
  | 0 => 1
  | r + 1 => e D k i r

theorem evenCyclotomicCoefficient_mem_coefficientAtLeast (i : I) (hi : D.parity i = 0) (n : ℕ) :
    evenCyclotomicCoefficient D k i n ∈ CoefficientAtLeast D k n := by
  cases n with
  | zero => exact mem_coefficientAtLeast_zero D k 1
  | succ r =>
    simpa [evenCyclotomicCoefficient, elementaryWeight, hi] using
      elementary_mem_coefficientAtLeast D k i r

def evenMonicCoefficient (i : I) (N : ℕ) (j : Fin (N + 1)) : SYM D k :=
  ((-1 : k) ^ (N - j.val)) • evenCyclotomicCoefficient D k i (N - j.val)

theorem evenMonicCoefficient_mem_coefficientAtLeast
    (i : I) (hi : D.parity i = 0) (N : ℕ) (j : Fin (N + 1)) :
    evenMonicCoefficient D k i N j ∈ CoefficientAtLeast D k (N - j.val) :=
  Submodule.smul_mem _ _ (evenCyclotomicCoefficient_mem_coefficientAtLeast D k i hi (N - j.val))

@[simp] theorem evenMonicCoefficient_top (i : I) (N : ℕ) :
    evenMonicCoefficient D k i N ⟨N, Nat.lt_succ_self N⟩ = 1 := by
  simp [evenMonicCoefficient, evenCyclotomicCoefficient]

end OddMath.SKM.SYM
