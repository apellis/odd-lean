import OddMath.QuiverHecke.CyclotomicAction.ELVCapRepresentativePowers
import Lean.Util.CollectAxioms
noncomputable section
namespace CapRepresentativePowersConsumer
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (j : {j : I // D.parity j = 1}) (v s : List I)
  (b : hom D Sc cutoff v (s ++ [j.1])) (g : hom D Sc cutoff (s ++ [j.1]) v)

example :
    (crossingInputDotAffine D Sc cutoff j v)^[2]
      (shortTensor D Sc cutoff j.1 v s v g ((ideal D Sc cutoff v (s ++ [j.1])).mkQ b)) =
      shortTensor D Sc cutoff j.1 v s v
        (appendMovingPower D Sc cutoff j.1 s 1 ≫ (appendMovingPower D Sc cutoff j.1 s 1 ≫ g))
        ((ideal D Sc cutoff v (s ++ [j.1])).mkQ b) := by
  simpa only [Function.iterate_succ_apply', Function.iterate_zero, id_eq,
    pow_two, SKM.zsign_mul_self', one_smul, twist_twist]
    using crossingInputDotAffine_iterate_representative D Sc cutoff j v s 2 b g
end CapRepresentativePowersConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCapRepresentativePowers
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
