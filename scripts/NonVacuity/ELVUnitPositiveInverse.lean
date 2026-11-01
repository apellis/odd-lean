import NonVacuity.ELVOffDiagonalRowSplitting
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitPositiveInverse
import Lean.Util.CollectAxioms
noncomputable section
namespace UnitPositiveInverseConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
open NonVacuity.SerreComplex OffDiagonalRowConsumer

abbrev U := ((BalancedInduction.induction (append datum scalars (fun _ => 3) movingOdd.1)).obj
  ((BalancedInduction.restriction (append datum scalars (fun _ => 3) movingOdd.1)).obj
    (oldRepresentable datum scalars (fun _ => 3)
      (⟨[true, false]⟩ : OldCategory datum scalars (fun _ => 3))))).obj
        (⟨[false, true]⟩ : OldCategory datum scalars (fun _ => 3))
abbrev W := offDiagonalBoundaryRowWindow datum scalars (fun _ => 3) movingOdd [true, false] [false, true]
abbrev O := Old datum scalars (fun _ => 3)
  ([true, false] ++ [movingOdd.1]) ([false, true] ++ [movingOdd.1])

def positive : (U × W) ≃ₗ[ℚ] O :=
  unitPositiveMatrixEquiv datum scalars (fun _ => 3) 0 movingOdd
    [true, false] [false, true] mixedPositiveHeight

example (x : U × W) : positive.symm (positive x) = x := positive.symm_apply_apply x
example (x : O) : positive (positive.symm x) = x := positive.apply_symm_apply x

example (z : U) (r : W) : positive (z, r) =
    -toCyclotomic datum scalars (fun _ => 3) movingOdd.1 [true, false] [false, true]
      (shiftedSourceCanonicalEquiv datum scalars (fun _ => 3) movingOdd [true, false] [false, true] z) +
      unitDotPolynomialMap datum scalars (fun _ => 3) movingOdd.1 [true, false] [false, true] r.val :=
  unitPositiveMatrixEquiv_apply datum scalars (fun _ => 3) 0 movingOdd [true, false] [false, true]
    mixedPositiveHeight z r
end UnitPositiveInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVUnitPositiveInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
