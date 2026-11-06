import OddMath.SKM.BWWGradedParameters
import NonVacuity.BWWScalars

/-! # Graded Brundan–Wang–Webster parameters

On the datum of `NonVacuity.BWWScalars` with symmetrizer `(1, 1)` and `ℚ` concentrated in
degree `0`: the Brundan–Ellis parameters `u³ + uv² + v³` are graded homogeneous as
Brundan–Wang–Webster parameters, while `u³ + v³ + 1` is not (its constant term would need
degree `6`).
-/

noncomputable section
namespace NonVacuity.BWWGradedParameters
open OddMath OddMath.SKM NonVacuity.BWWScalars

/-- The symmetrizer `(1, 1)`. -/
def symmetrizer : Symmetrizer datum where
  d := fun _ => 1
  pos := by intro i; norm_num
  symm := by intro i j; cases i <;> cases j <;> rfl

/-- `ℚ` concentrated in degree `0`. -/
def grading (n : ℕ) : Submodule ℚ ℚ := if n = 0 then ⊤ else ⊥

example : scalars.toBWW.GradedHomogeneous symmetrizer grading := by
  refine (Scalars.gradedHomogeneous_toBWW_iff _ _ _).mpr ⟨fun _ _ => by simp [grading], ?_⟩
  intro i j p q _ _ _ _ hs
  have h : i ≠ j ∧ p + q = 3 := by
    by_contra h
    exact hs (by simp [scalars, h])
  obtain ⟨hij, hpq⟩ := h
  refine ⟨0, ?_, by simp [grading]⟩
  have : (p : ℤ) + q = 3 := by exact_mod_cast hpq
  simp only [coefficientDegree, symmetrizer, d_ne hij]
  push_cast
  linarith

example : ¬constantTerm.GradedHomogeneous symmetrizer grading := by
  rintro ⟨-, h⟩
  obtain ⟨n, hn, hmem⟩ := h true false 0 0 (by decide) (by rw [d_ne (by decide)]; norm_num)
    (by rw [d_ne (by decide)]; norm_num) (by simp [constantTerm, support])
  simp only [coefficientDegree, symmetrizer, d_ne (show true ≠ false by decide)] at hn
  have hn6 : n = 6 := by omega
  subst hn6
  simp [grading, constantTerm, support] at hmem

end NonVacuity.BWWGradedParameters
