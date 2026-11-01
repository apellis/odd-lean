import OddMath.QuiverHecke.CyclotomicAction.ELVEvenCounitInverse
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace EvenCounitInverseConsumer
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
private def evenColour : {i : Bool // mixedDatum.parity i = 0} := ⟨false, rfl⟩
abbrev U (N : ℕ) (v t : List Bool) :=
  BalancedInduction.Obj (append mixedDatum mixedScalars (fun _ => N) false)
    (restrictedRepresentable mixedDatum mixedScalars (fun _ => N) false v).toFunctor
    (⟨t⟩ : OldCategory mixedDatum mixedScalars (fun _ => N))
abbrev Input := U 1 sourceWord targetWord
abbrev Output := Old mixedDatum mixedScalars (fun _ => 1) (sourceWord ++ [false]) (targetWord ++ [false])

theorem height : outputSDegree mixedDatum false sourceWord =
    endpointQPDegree mixedDatum (fun _ => 1) false sourceWord + 3 := by
  norm_num [outputSDegree, endpointQPDegree, appendQPDegree, SKM.Datum.dn,
    SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum, sourceWord,
    List.range_succ, List.getD]

def matrix : Input ≃ₗ[ℚ] (Output × (Fin 3 → Coeff)) :=
  evenCounitMatrixEquiv mixedDatum mixedScalars (fun _ => 1) 0 evenColour
    sourceWord targetWord 3 height

example (z : Input) : matrix.symm (matrix z) = z := matrix.symm_apply_apply z
example (z : Output × (Fin 3 → Coeff)) : matrix (matrix.symm z) = z := matrix.apply_symm_apply z

example (z : Input) : (matrix z).1 =
    -toCyclotomic mixedDatum mixedScalars (fun _ => 1) false sourceWord targetWord
      (evenSourceEquiv mixedDatum mixedScalars (fun _ => 1) evenColour sourceWord targetWord z) :=
  evenCounitMatrixEquiv_fst mixedDatum mixedScalars (fun _ => 1) 0 evenColour
    sourceWord targetWord 3 height z

example (z : Input) (r : Fin 3) : (matrix z).2 r =
    unshiftedCounitComponent mixedDatum mixedScalars (fun _ => 1) false sourceWord targetWord
      ((actualInductionDot mixedDatum mixedScalars (fun _ => 1) false
        (restrictedRepresentable mixedDatum mixedScalars (fun _ => 1) false sourceWord)
        (⟨targetWord⟩ : OldCategory mixedDatum mixedScalars (fun _ => 1)))^[r.val] z) :=
  evenCounitMatrixEquiv_cap mixedDatum mixedScalars (fun _ => 1) 0 evenColour
    sourceWord targetWord 3 height z r

/-- Zero height has no cap coordinates; both inverse products still hold. -/
def zeroMatrix : U 2 [false] [false] ≃ₗ[ℚ]
    (Old mixedDatum mixedScalars (fun _ => 2) ([false] ++ [false]) ([false] ++ [false]) ×
      (Fin 0 → Old mixedDatum mixedScalars (fun _ => 2) [false] [false])) :=
  evenCounitMatrixEquiv mixedDatum mixedScalars (fun _ => 2) 0 evenColour [false] [false] 0
    (by norm_num [evenColour, endpointQPDegree, outputSDegree, appendQPDegree, mixedDatum, List.range_succ, List.getD])

example (z : U 2 [false] [false]) : zeroMatrix.symm (zeroMatrix z) = z :=
  zeroMatrix.symm_apply_apply z

example (z : Old mixedDatum mixedScalars (fun _ => 2) ([false] ++ [false]) ([false] ++ [false]) ×
    (Fin 0 → Old mixedDatum mixedScalars (fun _ => 2) [false] [false])) :
    zeroMatrix (zeroMatrix.symm z) = z := zeroMatrix.apply_symm_apply z

end EvenCounitInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVEvenCounitInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
