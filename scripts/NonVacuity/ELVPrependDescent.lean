import OddMath.QuiverHecke.CyclotomicAction.ELVPrependDescent
import NonVacuity.ELVPrependCrossTail
import Lean.Util.CollectAxioms

noncomputable section
namespace ELVPrependDescentConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open ELVOld ELVPrependConsumer ELVPrependOldExtractionConsumer
open scoped TensorProduct DirectSum

/-- The continuation is arbitrary, not a prescribed same-source moving tail. -/
example (s : List Unit) (r : hom datum scalars (fun _ => 3) [()] s)
    (hr : r ∈ ideal datum scalars (fun _ => 3) [()] s)
    (h : hom datum scalars (fun _ => 3) (() :: s) [(), ()]) :
    prependExtractOldQuotient datum scalars (fun _ => 3) 1 movingIndex
      (insert datum scalars (fun _ => 3) () [()] s r ≫ h) = 0 :=
  prependExtractOldQuotient_old_generator datum scalars (fun _ => 3) 1 movingIndex r hr h

/-- The old Hom with different lengths is zero; no normal form is chosen in this case. -/
example (r : hom datum scalars (fun _ => 3) [()] []) : r = 0 := by
  by_contra hr
  obtain ⟨y⟩ := exists_oldIndex_of_ne_zero datum scalars (fun _ => 3) r hr
  have h := congrArg List.length y.tgt_cw
  simp only [length_tgt, List.length_cons, List.length_nil] at h
  omega

/-- An actual old relation vanishes with an inhomogeneous full exterior continuation. -/
example := prependExtractOldQuotient_old_generator datum scalars (fun _ => 3) 1 movingIndex
  (relation datum scalars (fun _ => 3) () []) (relation_mem datum scalars (fun _ => 3) () [])
  (((1 : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) datum (fun _ => 3)) + delta)
    ⊗ₜ[ℚ] prependElt datum scalars movingIndex)

example (z : Target datum scalars (fun _ => 3) () [()] [(), ()]) :=
  prependOldReconstruct_coordinateEquiv datum scalars (fun _ => 3) 1 () [()] [(), ()] z
example (f : PrependOldCoordinates datum scalars (fun _ => 3) () [()] [(), ()]) :=
  prependOldCoordinateEquiv_reconstruct datum scalars (fun _ => 3) 1 () [()] [(), ()] f
example (z : Target datum scalars (fun _ => 3) () [()] [(), ()])
    (q : PrependIdx.Tail () [()] [(), ()]) :=
  prependOldCoordinateEquiv_apply datum scalars (fun _ => 3) 1 z q

/-- Nonreduced coefficients with two invertible, without a flatness premise. -/
def scalarsNine : SKM.Scalars datum (ZMod 9) where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => ⟨⟨2, 5, by decide, by decide⟩, rfl⟩

example : (3 : ZMod 9) ≠ 0 ∧ (3 : ZMod 9) * 3 = 0 := by decide
example (N : ℕ) (z : Target datum scalarsNine (fun _ => N) () [] [()]) :=
  prependOldReconstruct_coordinateEquiv datum scalarsNine (fun _ => N) 1 () [] [()] z
example (f : PrependOldCoordinates datum scalarsNine (fun _ => 0) () [] [()]) :=
  prependOldCoordinateEquiv_reconstruct datum scalarsNine (fun _ => 0) 0 () [] [()] f

#print axioms prependExtractOldQuotient_old_generator
#print axioms prependExtractOldQuotient_relations
#print axioms prependOldCoordinateEquiv
#print axioms prependOldReconstruct_coordinateEquiv
#print axioms prependOldCoordinateEquiv_reconstruct
end ELVPrependDescentConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVPrependDescent
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Descent module was not imported"
  let mut count : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    count := count + 1
  if count == 0 then throwError "Empty descent declaration inventory"
  logInfo m!"Audited {count} owned descent declarations; all axioms allowed."
