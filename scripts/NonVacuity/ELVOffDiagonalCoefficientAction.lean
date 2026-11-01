import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalCoefficientAction
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
namespace OffDiagonalCoefficientActionConsumer
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v s t : List I) (g : hom D Sc cutoff s t)
    (z : AppendTarget D Sc cutoff i v (s ++ [i])) :
    appendC0 D Sc cutoff i v t
      (appendPostcomp D Sc cutoff i v (appendInsert D Sc cutoff i s t g) z) =
    offDiagonalCoefficientRightAction D Sc cutoff i 0 v s t
      ((ideal D Sc cutoff s t).mkQ g) (appendC0 D Sc cutoff i v s z) :=
  appendC0_postcomp_general D Sc cutoff i v s t g z

private abbrev AD := CyclotomicAction.AsymmetricParameters.datum
private abbrev AS := CyclotomicAction.AsymmetricParameters.scalars

/-- Distinct old words, odd moving colour, and arbitrary full coefficient arrow. -/
example (g : hom AD AS (fun _ => 12) [false, true] [true, false])
    (z : AppendTarget AD AS (fun _ => 12) false [false, true] ([false, true] ++ [false])) :
    appendC0 AD AS (fun _ => 12) false [false, true] [true, false]
      (appendPostcomp AD AS (fun _ => 12) false [false, true]
        (appendInsert AD AS (fun _ => 12) false [false, true] [true, false] g) z) =
      offDiagonalCoefficientRightAction AD AS (fun _ => 12) false 0
        [false, true] [false, true] [true, false]
        ((ideal AD AS (fun _ => 12) [false, true] [true, false]).mkQ g)
        (appendC0 AD AS (fun _ => 12) false [false, true] [false, true] z) :=
  appendC0_postcomp_general AD AS (fun _ => 12) false
    [false, true] [false, true] [true, false] g z
end OffDiagonalCoefficientActionConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalCoefficientAction
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
