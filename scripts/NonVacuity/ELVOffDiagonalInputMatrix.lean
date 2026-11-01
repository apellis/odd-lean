import NonVacuity.ELVOffDiagonalBoundarySnake
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalInputMatrix
import Lean.Util.CollectAxioms

noncomputable section
namespace OffDiagonalInputMatrixConsumer
open OddMath OddMath.QuiverHecke ELVOld ELVOld.CyclotomicCrossingTensor
open NonVacuity.SerreComplex OffDiagonalRowConsumer

def deepCutoff (i : Bool) : ℕ := if i then 1 else 3
def sourceWord : List Bool := [false, true, true, true]
def targetWord : List Bool := [true, false, true, true]
abbrev Coeff := Old datum scalars deepCutoff sourceWord targetWord
abbrev Input := Source datum scalars deepCutoff movingOdd.1 sourceWord targetWord
abbrev Output := Old datum scalars deepCutoff (sourceWord ++ [movingOdd.1]) (targetWord ++ [movingOdd.1])

theorem deepHeight :
    outputSDegree datum movingOdd.1 sourceWord =
      endpointQPDegree datum deepCutoff movingOdd.1 sourceWord + 3 := by
  have h := endpointQPDegree_sub_outputSDegree datum deepCutoff movingOdd.1 sourceWord
  norm_num [SKM.Datum.h, SKM.Datum.α, datum, deepCutoff, sourceWord, movingOdd] at h ⊢
  omega

/-- Three cap rows, mixed B2 content, different endpoint orders, and positive cutoffs. -/
def deepMatrix : Input ≃ₗ[ℚ] (Output × (Fin 3 → Coeff)) :=
  offDiagonalInputMatrixEquiv datum scalars deepCutoff 0 movingOdd
    sourceWord targetWord 3 deepHeight

example (z : Input) : deepMatrix.symm (deepMatrix z) = z := deepMatrix.symm_apply_apply z
example (z : Output × (Fin 3 → Coeff)) : deepMatrix (deepMatrix.symm z) = z :=
  deepMatrix.apply_symm_apply z

example (z : Input) (r : Fin 3) :
    offDiagonalInputCapVector datum scalars deepCutoff movingOdd sourceWord targetWord 3 z r =
      offDiagonalInputContraction datum scalars deepCutoff movingOdd sourceWord targetWord
        ((offDiagonalCrossingInputDot datum scalars deepCutoff movingOdd sourceWord targetWord)^[r.val] z) :=
  offDiagonalInputCapVector_apply datum scalars deepCutoff movingOdd sourceWord targetWord 3 z r

example (b : Coeff) :
    offDiagonalInputContractionAffine datum scalars deepCutoff movingOdd sourceWord targetWord
      ((offDiagonalCrossingInputDotAffine datum scalars deepCutoff movingOdd sourceWord targetWord)^[2]
        (offDiagonalBoundaryCrossCoordinates datum scalars deepCutoff 0 movingOdd sourceWord targetWord
          (offDiagonalLongExtraction datum scalars deepCutoff 0 movingOdd.1 sourceWord targetWord
            (offDiagonalCorrectedLift datum scalars deepCutoff 0 movingOdd sourceWord targetWord 0 b)))) =
      offDiagonalBoundaryLeadingEquiv datum scalars deepCutoff 0 movingOdd sourceWord targetWord 0 b :=
  offDiagonalInputContractionAffine_corrected_pivot datum scalars deepCutoff 0 movingOdd
    sourceWord targetWord 2 0 b (by have h := deepHeight; omega)

example (b : Coeff) :
    offDiagonalInputContractionAffine datum scalars deepCutoff movingOdd sourceWord targetWord
      ((offDiagonalCrossingInputDotAffine datum scalars deepCutoff movingOdd sourceWord targetWord)^[0]
        (offDiagonalBoundaryCrossCoordinates datum scalars deepCutoff 0 movingOdd sourceWord targetWord
          (offDiagonalLongExtraction datum scalars deepCutoff 0 movingOdd.1 sourceWord targetWord
            (offDiagonalCorrectedLift datum scalars deepCutoff 0 movingOdd sourceWord targetWord 0 b)))) = 0 :=
  offDiagonalInputContractionAffine_corrected_below datum scalars deepCutoff 0 movingOdd
    sourceWord targetWord 0 0 b (by have h := deepHeight; omega)

example (z : ShortTarget datum scalars deepCutoff movingOdd.1 sourceWord targetWord) :
    offDiagonalInputContraction datum scalars deepCutoff movingOdd sourceWord targetWord
      (q datum scalars deepCutoff movingOdd.1 sourceWord targetWord z) =
      offDiagonalInputContractionAffine datum scalars deepCutoff movingOdd sourceWord targetWord z :=
  offDiagonalInputContraction_q datum scalars deepCutoff movingOdd sourceWord targetWord z

example (z : ShortTarget datum scalars deepCutoff movingOdd.1 sourceWord targetWord) :
    offDiagonalCrossingInputDot datum scalars deepCutoff movingOdd sourceWord targetWord
      (q datum scalars deepCutoff movingOdd.1 sourceWord targetWord z) =
      q datum scalars deepCutoff movingOdd.1 sourceWord targetWord
        (offDiagonalCrossingInputDotAffine datum scalars deepCutoff movingOdd sourceWord targetWord z) :=
  offDiagonalCrossingInputDot_q datum scalars deepCutoff movingOdd sourceWord targetWord z

def zeroCutoff (i : Bool) : ℕ := if i then 2 else 3
def zeroSource : List Bool := [false, true, true]
def zeroTarget : List Bool := [true, false, true]
abbrev ZeroCoeff := Old datum scalars zeroCutoff zeroSource zeroTarget
abbrev ZeroInput := Source datum scalars zeroCutoff movingOdd.1 zeroSource zeroTarget
abbrev ZeroOutput := Old datum scalars zeroCutoff (zeroSource ++ [movingOdd.1]) (zeroTarget ++ [movingOdd.1])

theorem zeroHeight :
    outputSDegree datum movingOdd.1 zeroSource =
      endpointQPDegree datum zeroCutoff movingOdd.1 zeroSource + 0 := by
  have h := endpointQPDegree_sub_outputSDegree datum zeroCutoff movingOdd.1 zeroSource
  norm_num [SKM.Datum.h, SKM.Datum.α, datum, zeroCutoff, zeroSource, movingOdd] at h ⊢
  omega

/-- Zero cap rows at height zero, with positive cutoffs and repeated odd colour. -/
def zeroMatrix : ZeroInput ≃ₗ[ℚ] (ZeroOutput × (Fin 0 → ZeroCoeff)) :=
  offDiagonalInputMatrixEquiv datum scalars zeroCutoff 0 movingOdd
    zeroSource zeroTarget 0 zeroHeight

example (z : ZeroInput) : zeroMatrix.symm (zeroMatrix z) = z := zeroMatrix.symm_apply_apply z
example (z : ZeroOutput × (Fin 0 → ZeroCoeff)) : zeroMatrix (zeroMatrix.symm z) = z :=
  zeroMatrix.apply_symm_apply z

end OffDiagonalInputMatrixConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalInputOperators,
    `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalInputPivots,
    `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalInputMatrix,
    `OddMath.Algebra.FiniteTriangularCoordinates]
  for owner in owners do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} declarations in {owner}"
