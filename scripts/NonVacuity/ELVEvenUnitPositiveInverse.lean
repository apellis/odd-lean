import OddMath.QuiverHecke.CyclotomicAction.ELVEvenUnitPositiveInverse
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.CyclotomicCrossingTensor
namespace EvenUnitPositiveConsumer
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
private abbrev evenColour : {i : Bool // mixedDatum.parity i = 0} := ⟨false, rfl⟩
abbrev Input := BalancedInduction.Obj (append mixedDatum mixedScalars (fun _ => 4) false)
  (restrictedRepresentable mixedDatum mixedScalars (fun _ => 4) false [false,true]).toFunctor
  (⟨[true,false]⟩ : OldCategory mixedDatum mixedScalars (fun _ => 4))
abbrev Output := Old mixedDatum mixedScalars (fun _ => 4) ([false, true] ++ [false]) ([true, false] ++ [false])

theorem height : endpointQPDegree mixedDatum (fun _ => 4) false [false, true] =
    outputSDegree mixedDatum false [false, true] + 4 := by
  norm_num [outputSDegree, endpointQPDegree, appendQPDegree, SKM.Datum.dn,
    SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, mixedDatum, datum, List.range_succ, List.getD]

def positive : (Input × Window) ≃ₗ[ℚ] Output :=
  evenUnitPositiveMatrixEquiv mixedDatum mixedScalars (fun _ => 4) 1 evenColour
    [false, true] [true, false] (by change outputSDegree mixedDatum false [false,true] ≤ endpointQPDegree mixedDatum (fun _ => 4) false [false,true]; have h := height; omega)

example (x : Input × Window) : positive.symm (positive x) = x := positive.symm_apply_apply x
example (x : Output) : positive (positive.symm x) = x := positive.apply_symm_apply x

example (z : Input) (f : Window) : positive (z, f) =
    -toCyclotomic mixedDatum mixedScalars (fun _ => 4) false [false,true] [true,false]
      (evenSourceEquiv mixedDatum mixedScalars (fun _ => 4) evenColour [false,true] [true,false] z) +
        evenUnitDotPolynomialMap mixedDatum mixedScalars (fun _ => 4) evenColour
          [false,true] [true,false] f.val :=
  evenUnitPositiveMatrixEquiv_apply mixedDatum mixedScalars (fun _ => 4) 1 evenColour
    [false,true] [true,false] (by change outputSDegree mixedDatum false [false,true] ≤ endpointQPDegree mixedDatum (fun _ => 4) false [false,true]; have h := height; omega) z f

example (n : ℕ) (b : Coeff) :
    evenUnitDotPolynomialMap mixedDatum mixedScalars (fun _ => 4) evenColour
      [false,true] [true,false] (Finsupp.single n b) =
      inductionUnitDotColumn mixedDatum mixedScalars (fun _ => 4) false
        [false,true] [true,false] n b :=
  evenUnitDotPolynomialMap_single mixedDatum mixedScalars (fun _ => 4) evenColour
    [false,true] [true,false] n b

example : Window = Finsupp.supported Coeff ℚ (Set.Iio 4) :=
  evenBoundaryRowWindow_eq_height mixedDatum mixedScalars (fun _ => 4) false
    [false, true] [true, false] 4 height

end EvenUnitPositiveConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVEvenUnitPositiveInverse
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
