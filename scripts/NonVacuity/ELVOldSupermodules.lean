import OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OldSupermodulesConsumer
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
example (v w : OldCategory D Sc cutoff) (p : ZMod 2) (f : v ⟶ w) :
    proj k p f = oldProj D Sc cutoff v.word w.word p f :=
  oldCategory_proj D Sc cutoff v w p f
example (v w z : OldCategory D Sc cutoff) (f : w ⟶ z) (h : v ⟶ w) :
    (oldRepresentable D Sc cutoff v).map f h = h ≫ f :=
  oldRepresentable_map D Sc cutoff v w z f h
end OldSupermodulesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldSupermodules
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
