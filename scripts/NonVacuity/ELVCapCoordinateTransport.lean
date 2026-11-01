import OddMath.QuiverHecke.CyclotomicAction.ELVCapCoordinateTransport
import Lean.Util.CollectAxioms

noncomputable section
namespace CapCoordinateTransportConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    oldTwist D Sc cutoff (D.parity i) v t
      (appendC0InputDefect D Sc cutoff i v t
        (appendCrossingClass D Sc cutoff i v s t r g) 0) =
      -(SKM.zsign k (D.parity i * D.parity i)) •
        (ideal D Sc cutoff v t).mkQ (r ≫ twist k (D.parity i) g) :=
  oldTwist_inputDefect_crossing D Sc cutoff i v s t r g

example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (a : CyclotomicCrossingTensor.PprimeDomain D Sc cutoff j.1 v v) :
    appendC0InputDefect D Sc cutoff j.1 v v
      (CyclotomicCrossingTensor.shortCross D Sc cutoff j.1 v v
        (CyclotomicCrossingTensor.pprime D Sc cutoff j.1 v v a)) = 0 :=
  inputDefect_shortCross_pprime D Sc cutoff p j v a

example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    appendC0InputDefect D Sc cutoff j.1 v v
      (pMap D Sc cutoff j.1 v (v ++ [j.1])
        (CyclotomicCrossingTensor.sourceLongSection D Sc cutoff p j.1 v f)) =
      appendC0InputDefect D Sc cutoff j.1 v v (outputLiftBoundary D Sc cutoff p j v f) :=
  inputDefect_sourceLongSection_eq D Sc cutoff p j v f

example (j : {j : I // D.parity j = 1}) (v : List I)
    (z : CyclotomicCrossingTensor.ShortTarget D Sc cutoff j.1 v v) :
    CyclotomicCrossingTensor.inputContraction D Sc cutoff j v
      (CyclotomicCrossingTensor.q D Sc cutoff j.1 v v z) =
      appendC0InputDefect D Sc cutoff j.1 v v
        (CyclotomicCrossingTensor.shortCross D Sc cutoff j.1 v v z) 0 :=
  CyclotomicCrossingTensor.inputContraction_q D Sc cutoff j v z
end CapCoordinateTransportConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCapCoordinateTransport
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
