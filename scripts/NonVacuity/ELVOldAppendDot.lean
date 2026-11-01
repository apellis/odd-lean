import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
namespace OldAppendDotConsumer
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
example (i : I) : IsSupernatural k (D.parity i) (oldAppendDotComponent D Sc cutoff i) :=
  oldAppendDot_supernatural D Sc cutoff i
example (i : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i s =
      (ideal D Sc cutoff _ _).mkQ (appendMovingPower D Sc cutoff i s.word 1) :=
  oldAppendDotComponent_eq D Sc cutoff i s
end OldAppendDotConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
