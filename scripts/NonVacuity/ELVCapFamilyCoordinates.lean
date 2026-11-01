import NonVacuity.ELVCounitInputInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVCapFamilyCoordinates
import Lean.Util.CollectAxioms
noncomputable section
namespace CapFamilyCoordinatesConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
open NonVacuity.SerreComplex OffDiagonalRowConsumer OffDiagonalInputMatrixConsumer
open CounitInputInverseConsumer

abbrev F := (a : Option (Fin 3)) →
  (capMatrixFamily datum scalars deepCutoff movingOdd.1
    (oldRepresentable datum scalars deepCutoff
      (⟨sourceWord⟩ : OldCategory datum scalars deepCutoff)) 3 a).obj
        (⟨targetWord⟩ : OldCategory datum scalars deepCutoff)
def matrix : Unshifted ≃ₗ[ℚ] F :=
  capFamilyComponentEquiv datum scalars deepCutoff 0 movingOdd sourceWord targetWord 3 deepHeight

example (z : Unshifted) : matrix.symm (matrix z) = z := matrix.symm_apply_apply z
example (y : F) : matrix (matrix.symm y) = y := matrix.apply_symm_apply y

example (z : Unshifted) :
    capFamilyComponentCoordinates datum scalars deepCutoff movingOdd.1 sourceWord targetWord 3
      (matrix z) = ordinaryMatrix z :=
  capFamilyComponentEquiv_coordinates datum scalars deepCutoff 0 movingOdd
    sourceWord targetWord 3 deepHeight z

example (z : Unshifted) :
    (capFamilyComponentCoordinates datum scalars deepCutoff movingOdd.1 sourceWord targetWord 3
      (matrix z)).1 = -toCyclotomic datum scalars deepCutoff movingOdd.1 sourceWord targetWord
        (shiftedSourceCanonicalEquiv datum scalars deepCutoff movingOdd sourceWord targetWord z) :=
  capFamilyComponentEquiv_fst datum scalars deepCutoff 0 movingOdd
    sourceWord targetWord 3 deepHeight z

example (z : Unshifted) (r : Fin 3) :
    (capFamilyComponentCoordinates datum scalars deepCutoff movingOdd.1 sourceWord targetWord 3
      (matrix z)).2 r =
      ((BalancedInduction.adjunctionCounit (append datum scalars deepCutoff movingOdd.1)).app
        (oldRepresentable datum scalars deepCutoff
          (⟨sourceWord⟩ : OldCategory datum scalars deepCutoff))).total
          (⟨targetWord⟩ : OldCategory datum scalars deepCutoff)
          ((actualInductionDot datum scalars deepCutoff movingOdd.1
            ((BalancedInduction.restriction (append datum scalars deepCutoff movingOdd.1)).obj
              (oldRepresentable datum scalars deepCutoff
                (⟨sourceWord⟩ : OldCategory datum scalars deepCutoff)))
            (⟨targetWord⟩ : OldCategory datum scalars deepCutoff))^[r.val] z) :=
  capFamilyComponentEquiv_cap datum scalars deepCutoff 0 movingOdd sourceWord targetWord 3 deepHeight z r

end CapFamilyCoordinatesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCapFamilyCoordinates
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
