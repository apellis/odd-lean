import OddMath.QuiverHecke.CyclotomicAction.ELVCrossingInputDot
import Lean.Util.CollectAxioms

noncomputable section
namespace CrossingInputDotConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (j : {j : I // D.parity j = 1}) (v : List I)

example (z : ShortTarget D Sc cutoff j.1 v v) :
    crossingInputDot D Sc cutoff j v (q D Sc cutoff j.1 v v z) =
      q D Sc cutoff j.1 v v (crossingInputDotAffine D Sc cutoff j v z) :=
  crossingInputDot_q D Sc cutoff j v z

example (z : ShortTarget D Sc cutoff j.1 v v) :
    shortCross D Sc cutoff j.1 v v (crossingInputDotAffine D Sc cutoff j v z) =
      appendMovingPowerTarget D Sc cutoff j.1 v (v ++ [j.1]) 1
        (shortCross D Sc cutoff j.1 v v z) -
      appendOutputEmbedding D Sc cutoff j.1 v v
        (appendC0InputDefect D Sc cutoff j.1 v v (shortCross D Sc cutoff j.1 v v z)) :=
  shortCross_crossingInputDotAffine D Sc cutoff j v z

example (a : PprimeDomain D Sc cutoff j.1 v v) :
    crossingInputDotAffine D Sc cutoff j v (pprime D Sc cutoff j.1 v v a) ∈
      LinearMap.range (pprime D Sc cutoff j.1 v v) :=
  crossingInputDotAffine_pprime D Sc cutoff j v a
end CrossingInputDotConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCrossingInputDot
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
