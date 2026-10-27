import OddMath.SKM.JointScalarDescent
import Mathlib.Algebra.Ring.Prod

/-! Both projections are necessary over a ring with zero divisors. -/

noncomputable section
open OddMath.SKM

private def projection (j : Bool) : (ℚ × ℚ) →+* ℚ :=
  if j then RingHom.fst ℚ ℚ else RingHom.snd ℚ ℚ

private theorem projections_separate (r : ℚ × ℚ)
    (h : ∀ j, projection j r = 0) : r = 0 := by
  apply Prod.ext
  · exact h true
  · exact h false

private theorem fiber_independent (j : Bool) :
    LinearIndependent ℚ (fun _ : Unit => (projection j).toSemilinearMap (1 : ℚ × ℚ)) := by
  rw [linearIndependent_unique_iff]
  simp [projection]

private theorem source_spanning :
    Submodule.span (ℚ × ℚ) (Set.range (fun _ : Unit => (1 : ℚ × ℚ))) = ⊤ := by
  have he : (fun _ : Unit => (1 : ℚ × ℚ)) =
      (Module.Basis.singleton Unit (ℚ × ℚ) : Unit → ℚ × ℚ) := by
    funext i
    exact (Module.Basis.singleton_apply _ _ i).symm
  rw [he]
  exact (Module.Basis.singleton Unit (ℚ × ℚ)).span_eq

example : Module.Basis Unit (ℚ × ℚ) (ℚ × ℚ) :=
  basisOfJointScalarImages (fun _ : Bool => ℚ) (fun _ : Bool => ℚ)
    projection projections_separate (fun _ : Unit => (1 : ℚ × ℚ))
    (fun j => (projection j).toSemilinearMap) fiber_independent source_spanning

-- Neither fiber map is injective: its kernel contains a nonzero idempotent.
example : ¬ Function.Injective (projection true) := by
  intro h
  have he := h (show projection true (0, 1) = projection true (0, 0) by rfl)
  have he' := congrArg Prod.snd he
  norm_num at he'

example : ¬ Function.Injective (projection false) := by
  intro h
  have he := h (show projection false (1, 0) = projection false (0, 0) by rfl)
  have he' := congrArg Prod.fst he
  norm_num at he'

#print axioms OddMath.SKM.linearIndependent_of_joint_scalar_images
#print axioms OddMath.SKM.basisOfJointScalarImages
#print axioms OddMath.SKM.basisOfJointScalarImages_apply
