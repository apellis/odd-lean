import OddMath.QuiverHecke.CyclotomicAction.ELVEvenPositiveCrossing
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace EvenPositiveCrossingConsumer
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



abbrev Coeff := Old mixedDatum mixedScalars (fun _ => 4) [false, true] [true, false]
abbrev Window := evenBoundaryRowWindow mixedDatum mixedScalars (fun _ => 4) false
  [false, true] [true, false]
abbrev Input := Source mixedDatum mixedScalars (fun _ => 4) false [false, true] [true, false]
abbrev Output := Old mixedDatum mixedScalars (fun _ => 4) ([false, true] ++ [false]) ([true, false] ++ [false])

theorem height : endpointQPDegree mixedDatum (fun _ => 4) false [false, true] =
    outputSDegree mixedDatum false [false, true] + 4 := by
  norm_num [outputSDegree, endpointQPDegree, appendQPDegree, SKM.Datum.dn,
    SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum, List.range_succ, List.getD]

def positive : (Input × Window) ≃ₗ[ℚ] Output :=
  evenPositiveCrossingEquiv mixedDatum mixedScalars (fun _ => 4) 1 false rfl
    [false, true] [true, false] (by have h := height; omega)

example (x : Input × Window) : positive.symm (positive x) = x := positive.symm_apply_apply x
example (x : Output) : positive (positive.symm x) = x := positive.apply_symm_apply x

example (z : Input) (f : Window) : positive (z, f) =
    toCyclotomic mixedDatum mixedScalars (fun _ => 4) false [false, true] [true, false] z +
      canonicalAppendTarget mixedDatum mixedScalars (fun _ => 4) false [false, true]
        ([true, false] ++ [false])
        (appendOutputEmbedding mixedDatum mixedScalars (fun _ => 4) false [false, true] [true, false] f) := rfl

example : Window = Finsupp.supported Coeff ℚ (Set.Iio 4) :=
  evenBoundaryRowWindow_eq_height mixedDatum mixedScalars (fun _ => 4) false
    [false, true] [true, false] 4 height

end EvenPositiveCrossingConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVEvenPositiveCrossing
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
