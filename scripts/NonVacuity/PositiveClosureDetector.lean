import OddMath.SKM.PositiveClosureDetector
import Mathlib.Data.Rat.Defs

noncomputable section
namespace NonVacuity.PositiveClosureDetector
open OddMath.SKM.OrientedReduction

/-- A genuine positive correction: every polynomial coefficient is also
added one position higher, with no finite bound on the label set. -/
def onePlusShift : (ℕ →₀ ℚ) →ₗ[ℚ] (ℕ →₀ ℚ) :=
  LinearMap.id + Finsupp.lmapDomain ℚ ℚ Nat.succ

theorem onePlusShift_injective : Function.Injective onePlusShift := by
  apply injective_of_positive_closure id onePlusShift LinearMap.id LinearMap.id
    (fun _ _ h => h)
  intro i p
  refine ⟨Finsupp.single (i + 1) p, ?_, ?_⟩
  · intro j hj
    have hji : j = i + 1 := by
      by_contra h
      simp [Finsupp.single_eq_of_ne h] at hj
    subst j
    exact Nat.lt_succ_self _
  · simp [onePlusShift, Finsupp.lmapDomain]

#print axioms injective_of_positive_closure
#print axioms onePlusShift_injective
end NonVacuity.PositiveClosureDetector
