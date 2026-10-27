import OddMath.SKM.SeparatingFields
import OddMath.SKM.MoreGenerators
import Mathlib.Algebra.Ring.Prod

/-! The prime-quotient fraction fields detect both components of a reduced ring
with zero divisors. -/

noncomputable section
open OddMath.SKM

private abbrev A := ℚ × ℚ

private example : IsReduced A := inferInstance
private example : Algebra ℚ A := inferInstance

private example : ((1, 0) : A) * (0, 1) = 0 ∧
    ((1, 0) : A) ≠ 0 ∧ ((0, 1) : A) ≠ 0 := by
  norm_num

private theorem fiber_independent (p : PrimeSpectrum A) :
    LinearIndependent (primeFractionField A p)
      (fun _ : Unit => (primeFractionMap A p).toSemilinearMap (1 : A)) := by
  rw [linearIndependent_unique_iff]
  simp

private theorem source_spanning :
    Submodule.span A (Set.range (fun _ : Unit => (1 : A))) = ⊤ := by
  have he : (fun _ : Unit => (1 : A)) =
      (Module.Basis.singleton Unit A : Unit → A) := by
    funext i
    exact (Module.Basis.singleton_apply _ _ i).symm
  rw [he]
  exact (Module.Basis.singleton Unit A).span_eq

example : Module.Basis Unit A A :=
  basisOfJointScalarImages (primeFractionField A) (primeFractionField A)
    (primeFractionMap A) (primeFractionMaps_separate A)
    (fun _ : Unit => (1 : A))
    (fun p => (primeFractionMap A p).toSemilinearMap)
    fiber_independent source_spanning

#print axioms OddMath.SKM.primeFractionMaps_separate
