import OddMath.QuiverHecke.CyclotomicAction.ELVEvenInputMatrix
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace EvenInputMatrixConsumer
open CyclotomicAction.AsymmetricParameters
private def mixedDatum : SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }

private def mixedScalars : SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num



def sourceWord : List Bool := [false, false, false, true]
def targetWord : List Bool := [true, false, false, false]
abbrev Coeff := Old mixedDatum mixedScalars (fun _ => 1) sourceWord targetWord
abbrev Input := Source mixedDatum mixedScalars (fun _ => 1) false sourceWord targetWord
abbrev Output := Old mixedDatum mixedScalars (fun _ => 1) (sourceWord ++ [false]) (targetWord ++ [false])

theorem height : outputSDegree mixedDatum false sourceWord =
    endpointQPDegree mixedDatum (fun _ => 1) false sourceWord + 3 := by
  norm_num [outputSDegree, endpointQPDegree, appendQPDegree, SKM.Datum.dn,
    SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum, sourceWord,
    List.range_succ, List.getD]

def matrix : Input ≃ₗ[ℚ] (Output × (Fin 3 → Coeff)) :=
  evenInputMatrixEquiv mixedDatum mixedScalars (fun _ => 1) 0 false rfl
    sourceWord targetWord 3 height

example (z : Input) : matrix.symm (matrix z) = z := matrix.symm_apply_apply z
example (z : Output × (Fin 3 → Coeff)) : matrix (matrix.symm z) = z := matrix.apply_symm_apply z

example (z : Input) : (matrix z).1 =
    toCyclotomic mixedDatum mixedScalars (fun _ => 1) false sourceWord targetWord z := rfl

example (z : Input) (r : Fin 3) : (matrix z).2 r =
    evenInputContraction mixedDatum mixedScalars (fun _ => 1) false rfl sourceWord targetWord
      ((evenCrossingInputDot mixedDatum mixedScalars (fun _ => 1) false rfl sourceWord targetWord)^[r.val] z) :=
  evenInputCapVector_apply mixedDatum mixedScalars (fun _ => 1) false rfl sourceWord targetWord 3 z r

example (b : Coeff) :
    evenInputContractionAffine mixedDatum mixedScalars (fun _ => 1) false sourceWord targetWord
      ((evenCrossingInputDotAffine mixedDatum mixedScalars (fun _ => 1) false sourceWord targetWord)^[2]
        (evenBoundaryCrossCoordinates mixedDatum mixedScalars (fun _ => 1) 0 false sourceWord targetWord
          (Finsupp.single 0 b))) =
      evenOffDiagonalBoundaryLeadingEquiv mixedDatum mixedScalars (fun _ => 1) 0 false sourceWord targetWord b :=
  evenInputContractionAffine_pivot mixedDatum mixedScalars (fun _ => 1) 0 false rfl
    sourceWord targetWord 2 0 b (by have h := height; omega)

example (b : Coeff) :
    evenInputContractionAffine mixedDatum mixedScalars (fun _ => 1) false sourceWord targetWord
      ((evenCrossingInputDotAffine mixedDatum mixedScalars (fun _ => 1) false sourceWord targetWord)^[0]
        (evenBoundaryCrossCoordinates mixedDatum mixedScalars (fun _ => 1) 0 false sourceWord targetWord
          (Finsupp.single 0 b))) = 0 :=
  evenInputContractionAffine_below mixedDatum mixedScalars (fun _ => 1) 0 false rfl
    sourceWord targetWord 0 0 b (by have h := height; omega)


/-- Height zero is included with no cap coordinates. -/
def zeroMatrix : Source mixedDatum mixedScalars (fun _ => 2) false [false] [false] ≃ₗ[ℚ]
    (Old mixedDatum mixedScalars (fun _ => 2) ([false] ++ [false]) ([false] ++ [false]) ×
      (Fin 0 → Old mixedDatum mixedScalars (fun _ => 2) [false] [false])) :=
  evenInputMatrixEquiv mixedDatum mixedScalars (fun _ => 2) 0 false rfl [false] [false] 0
    (by norm_num [endpointQPDegree, outputSDegree, appendQPDegree, mixedDatum, List.range_succ, List.getD])

example (z : Source mixedDatum mixedScalars (fun _ => 2) false [false] [false]) :
    zeroMatrix.symm (zeroMatrix z) = z := zeroMatrix.symm_apply_apply z

example (z : Old mixedDatum mixedScalars (fun _ => 2) ([false] ++ [false]) ([false] ++ [false]) ×
    (Fin 0 → Old mixedDatum mixedScalars (fun _ => 2) [false] [false])) :
    zeroMatrix (zeroMatrix.symm z) = z := zeroMatrix.apply_symm_apply z

end EvenInputMatrixConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVEvenInputMatrix,
      `OddMath.Algebra.LowPolynomialCoordinates,
      `OddMath.Algebra.FiniteTriangularCoordinates] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner"
    for name in names do
      for ax in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited ALL {names.size} declarations of {owner}"
