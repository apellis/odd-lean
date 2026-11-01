import NonVacuity.ELVOffDiagonalInputMatrix
import OddMath.QuiverHecke.CyclotomicAction.ELVCounitInputInverse
import Lean.Util.CollectAxioms

noncomputable section
namespace CounitInputInverseConsumer
open OddMath OddMath.QuiverHecke ELVOld ELVOld.CyclotomicCrossingTensor
open NonVacuity.SerreComplex OffDiagonalRowConsumer OffDiagonalInputMatrixConsumer

abbrev Unshifted := (actualUnshiftedSourceModule datum scalars deepCutoff movingOdd.1
  sourceWord).obj (⟨targetWord⟩ : OldCategory datum scalars deepCutoff)

def ordinaryMatrix : Unshifted ≃ₗ[ℚ] (Output × (Fin 3 → Coeff)) :=
  counitInputMatrixEquiv datum scalars deepCutoff 0 movingOdd
    sourceWord targetWord 3 deepHeight

example (z : Unshifted) : ordinaryMatrix.symm (ordinaryMatrix z) = z :=
  ordinaryMatrix.symm_apply_apply z

example (z : Output × (Fin 3 → Coeff)) : ordinaryMatrix (ordinaryMatrix.symm z) = z :=
  ordinaryMatrix.apply_symm_apply z

example (z : Unshifted) :
    (ordinaryMatrix z).1 = -toCyclotomic datum scalars deepCutoff movingOdd.1
      sourceWord targetWord
      (shiftedSourceCanonicalEquiv datum scalars deepCutoff movingOdd sourceWord targetWord z) :=
  counitInputMatrixEquiv_fst datum scalars deepCutoff 0 movingOdd sourceWord targetWord 3 deepHeight z

example (z : Unshifted) (r : Fin 3) :
    (ordinaryMatrix z).2 r =
      ((BalancedInduction.adjunctionCounit (append datum scalars deepCutoff movingOdd.1)).app
        (oldRepresentable datum scalars deepCutoff
          (⟨sourceWord⟩ : OldCategory datum scalars deepCutoff))).total
          (⟨targetWord⟩ : OldCategory datum scalars deepCutoff)
          ((actualInductionDot datum scalars deepCutoff movingOdd.1
            ((BalancedInduction.restriction (append datum scalars deepCutoff movingOdd.1)).obj
              (oldRepresentable datum scalars deepCutoff
                (⟨sourceWord⟩ : OldCategory datum scalars deepCutoff)))
            (⟨targetWord⟩ : OldCategory datum scalars deepCutoff))^[r.val] z) :=
  counitInputMatrixEquiv_cap datum scalars deepCutoff 0 movingOdd sourceWord targetWord 3 deepHeight z r

example (b : Coeff) : counitInputRowEquiv datum scalars deepCutoff sourceWord targetWord 2 b =
    -oldTwist datum scalars deepCutoff 1 sourceWord targetWord b := by
  norm_num [counitInputRowEquiv_apply, capRowSign]
  rw [show (3 : ZMod 2) = 1 by decide]

end CounitInputInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCounitInputInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
