import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridDots
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendDot
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction BalancedInduction CyclotomicCrossingTensor
namespace InductionGridDotsConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
/-- Both moving parities, the chosen old induction comparison, and all module vectors. -/
example (i : Bool) (M : Superfunctor ℚ (OldContentCategory D Sc cut []) (SVec ℚ)) :=
  inductionComp_inner_dot (oldContentAppend D Sc cut [] i) (oldContentAppend D Sc cut [i] i)
    (oldContentAppendDot_supernatural D Sc cut [] i) M
example (i : Bool) (M : Superfunctor ℚ (OldContentCategory D Sc cut []) (SVec ℚ)) :=
  inductionComp_outer_dot (oldContentAppend D Sc cut [] i) (oldContentAppend D Sc cut [i] i)
    (oldContentAppendDot_supernatural D Sc cut [i] i) M
end InductionGridDotsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridDots
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
