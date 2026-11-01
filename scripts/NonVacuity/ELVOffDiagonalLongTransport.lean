import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongTransport
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
namespace OffDiagonalLongTransportConsumer
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev cutoff : Bool → ℕ := fun _ => 12
example (p : ZMod 2) (b : Old D Sc cutoff [false, true] [true, false]) :
    offDiagonalLongSection D Sc cutoff p false [false, true] [true, false]
      (Finsupp.single 0 b) =
      pair D Sc cutoff p false (bareUFull D Sc cutoff false [true, false]) b :=
  offDiagonalLongSection_single_zero_pair D Sc cutoff p false _ _ b
example (p : ZMod 2) (r : hom D Sc cutoff [false, true] [true, false]) :
    projection D Sc cutoff false [false, true] ([true, false] ++ [false])
      (bareUFull D Sc cutoff false [false, true] ≫ appendInsert D Sc cutoff false
        [false, true] [true, false]
        (twist ℚ (p + D.parity false * wordSumParity D [false, true]) r)) -
      offDiagonalLongSection D Sc cutoff p false [false, true] [true, false]
        (Finsupp.single 0 ((ideal D Sc cutoff [false, true] [true, false]).mkQ r)) ∈
      chronologicalShortSpan D Sc cutoff false [false, true] [true, false] :=
  offDiagonalLongSection_zero_transport D Sc cutoff p false _ _ r
end OffDiagonalLongTransportConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalLongTransport
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
