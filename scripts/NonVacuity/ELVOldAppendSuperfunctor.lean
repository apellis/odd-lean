import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendSuperfunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionParityComparison
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OldAppendSuperfunctorConsumer
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v w : OldCategory D Sc cutoff) (p : ZMod 2) (f : v ⟶ w)
    (hf : f ∈ parity (R := k) v w p) :
    (append D Sc cutoff i).map f ∈
      parity (R := k) ((append D Sc cutoff i).obj v) ((append D Sc cutoff i).obj w) p :=
  map_mem (append D Sc cutoff i) hf

example (i : I) (v : OldCategory D Sc cutoff) :
    let A := append D Sc cutoff i
    let N := oldRepresentable D Sc cutoff v
    (adjunctionParitySourceIso A N).hom ≫
      (adjunctionCounit A).app (supermoduleParityObj N) ≫ (supermoduleParityIso N).hom =
      (adjunctionCounit A).app N := by
  exact adjunctionParitySourceIso_counit (append D Sc cutoff i) (oldRepresentable D Sc cutoff v)

end OldAppendSuperfunctorConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendSuperfunctor
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
