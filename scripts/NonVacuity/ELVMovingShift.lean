import OddMath.QuiverHecke.CyclotomicAction.ELVMovingShift
import NonVacuity.ELVPrependDescent
import Lean.Util.CollectAxioms

noncomputable section
namespace ELVMovingShiftConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open ELVOld ELVPrependConsumer ELVPrependOldExtractionConsumer ELVPrependDescentConsumer
open scoped TensorProduct DirectSum

/-- Full exterior coefficients, an old odd strand, and total balance parity one. -/
example (b : Old datum scalars (fun _ => 3) [()] movingIndex.oldTarget) :=
  movingPower_pair_shift datum scalars (fun _ => 3) 1 movingIndex 2
    (by decide) b

/-- The moving square is tested on every class, not only scalar coefficients. -/
example (q : PrependIdx.Tail () [()] [(), ()])
    (z : Target datum scalars (fun _ => 3) () [()] [(), ()]) :=
  movingSquare_coordinate_shift datum scalars (fun _ => 3) 1 q z

/-- Nonreduced ground ring, arbitrary cutoff, and no flatness premise. -/
example (N : ℕ) (q : PrependIdx.Tail () [] [()])
    (z : Target datum scalarsNine (fun _ => N) () [] [()]) :=
  movingSquare_coordinate_shift datum scalarsNine (fun _ => N) 0 q z

/-- Even-colour shift is checked without replacing the full coefficient algebra. -/
example {I X k : Type} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (N : I → ℕ)
    (i : I) (hi : D.parity i = 0) (v w : List I)
    (q : PrependIdx.Tail i v w) (z : Target D Sc N i v w) :=
  movingEvenDot_coordinate_shift D Sc N 1 hi q z

/-- The actual old action retains an inhomogeneous exterior coefficient. -/
example (b : Old datum scalars (fun _ => 3) [()] movingIndex.oldTarget) :=
  oldSourceTarget_pair datum scalars (fun _ => 3) 1 movingIndex
    (((1 : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) datum (fun _ => 3)) + delta)
      ⊗ₜ[ℚ] (𝟙 ((pres datum scalars).obj (ob datum [()])))) b

/-- The source last square minus the moving square is the operator actually cancelled. -/
example (h : hom datum scalars (fun _ => 3) [(), ()] [(), ()]) :=
  lastDotDifference_projection datum scalars (fun _ => 3) () [()] [(), ()]
    (by decide) 2 (by decide) h

example := lastDotSquareDifference_injective datum scalars (fun _ => 3) 1 () [()] [(), ()]
example (N : ℕ) :=
  lastDotSquareDifference_injective datum scalarsNine (fun _ => N) 0 () [()] [(), ()]

example {I X k : Type} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (N : I → ℕ)
    (i : I) (hi : D.parity i = 0) (v w : List I) :=
  lastDotEvenDifference_injective D Sc N 1 i hi v w

#print axioms oldSourceTarget_pair
#print axioms oldSourceTarget_above
#print axioms lastDotDifference_projection
#print axioms lastDotSquareDifference_injective
#print axioms lastDotEvenDifference_injective
#print axioms movingPower_pair_shift
#print axioms movingPower_coordinate_shift
#print axioms movingSquare_coordinate_shift
#print axioms movingEvenDot_coordinate_shift
end ELVMovingShiftConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVMovingShift
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Moving-shift module was not imported"
  let mut count : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    count := count + 1
  if count == 0 then throwError "Empty moving-shift declaration inventory"
  logInfo m!"Audited {count} owned moving-shift declarations; all axioms allowed."
