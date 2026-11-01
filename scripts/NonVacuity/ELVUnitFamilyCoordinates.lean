import NonVacuity.ELVUnitPositiveInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitFamilyCoordinates
import Lean.Util.CollectAxioms
noncomputable section
namespace UnitFamilyCoordinatesConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
open NonVacuity.SerreComplex OffDiagonalRowConsumer

theorem height : endpointQPDegree datum (fun _ => 3) movingOdd.1 [true, false] =
    outputSDegree datum movingOdd.1 [true, false] + 3 := by
  have h := endpointQPDegree_sub_outputSDegree datum (fun _ => 3) movingOdd.1 [true, false]
  norm_num [SKM.Datum.h, SKM.Datum.α, datum, movingOdd] at h ⊢
  omega

abbrev H := oldRepresentable datum scalars (fun _ => 3)
  (⟨[true, false]⟩ : OldCategory datum scalars (fun _ => 3))
abbrev F := (a : Option (Fin 3)) →
  (unitMatrixFamily datum scalars (fun _ => 3) movingOdd.1 H 3 a).obj
    (⟨[false, true]⟩ : OldCategory datum scalars (fun _ => 3))
abbrev O := Old datum scalars (fun _ => 3)
  ([true, false] ++ [movingOdd.1]) ([false, true] ++ [movingOdd.1])

def matrix : F ≃ₗ[ℚ] O := unitFamilyComponentEquiv datum scalars (fun _ => 3)
  0 movingOdd [true, false] [false, true] 3 height

example (x : F) : matrix.symm (matrix x) = x := matrix.symm_apply_apply x
example (y : O) : matrix (matrix.symm y) = y := matrix.apply_symm_apply y

example (x : F) : matrix x =
    -toCyclotomic datum scalars (fun _ => 3) movingOdd.1 [true, false] [false, true]
      (shiftedSourceCanonicalEquiv datum scalars (fun _ => 3) movingOdd [true, false] [false, true]
        (unitFamilyPlainCoordinates datum scalars (fun _ => 3) movingOdd.1
          [true, false] [false, true] 3 x).1) +
      ∑ r : Fin 3, inductionUnitDotColumn datum scalars (fun _ => 3) movingOdd.1
        [true, false] [false, true] r.val
        ((unitFamilyPlainCoordinates datum scalars (fun _ => 3) movingOdd.1
          [true, false] [false, true] 3 x).2 r) :=
  unitFamilyComponentEquiv_apply datum scalars (fun _ => 3) 0 movingOdd
    [true, false] [false, true] 3 height x

example (b : Fin 3 → Old datum scalars (fun _ => 3) [true, false] [false, true]) :
    unitCoefficientDiagonal datum scalars (fun _ => 3) 1 [true, false] [false, true] 3 b ⟨2, by omega⟩ =
      -b ⟨2, by omega⟩ := by
  rw [unitCoefficientDiagonal_apply, inductionUnitDotSign_eq]
  norm_num
end UnitFamilyCoordinatesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVUnitFamilyCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
