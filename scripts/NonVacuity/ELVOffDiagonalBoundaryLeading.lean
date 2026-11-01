import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundaryLeading
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
namespace OffDiagonalBoundaryLeadingConsumer
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev cutoff : Bool → ℕ := fun _ => 12
private def j : {j : Bool // D.parity j = 1} := ⟨false, rfl⟩
example (p : ZMod 2) (d n : ℕ) (c : Old D Sc cutoff [false, true] [true, false])
    (hn : n + outputSDegree D j.1 [false, true] =
      d + endpointQPDegree D cutoff j.1 [false, true]) :
    offDiagonalPolynomialBoundary D Sc cutoff p j.1 [false, true] [true, false]
      (offDiagonalLongExtraction D Sc cutoff p j.1 [false, true] [true, false]
        (offDiagonalCorrectedLift D Sc cutoff p j [false, true] [true, false] d c)) n =
      offDiagonalBoundaryLeadingEquiv D Sc cutoff p j [false, true] [true, false] n c :=
  offDiagonalBoundary_corrected_top D Sc cutoff p j _ _ d n c hn
example (p : ZMod 2) (n : ℕ) :
    Function.Bijective (offDiagonalBoundaryLeadingEquiv D Sc cutoff p j
      [false, true] [true, false] n) :=
  (offDiagonalBoundaryLeadingEquiv D Sc cutoff p j _ _ n).bijective
end OffDiagonalBoundaryLeadingConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundaryLeading
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
