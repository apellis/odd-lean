import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPairAppend
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace WeightedPairAppendConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)
private abbrev J (i : Bool) := CyclotomicCrossingTensor.append D Sc cut i

private def oddIndex : SKM.SYM.CoefficientIndex D := (0, {⟨true, rfl⟩})

/-- Both moving parities, equal and distinct colours retain an odd coefficient. -/
example (i j : Bool) := pairAppend_oldCoefficientBasis D Sc cut i j [false, true] oddIndex

example (i j : Bool) := pairAppend_truncate D Sc cut 8 i j

/-- The annihilator premise is supplied by the actual weighted quotient. -/
example (i j : Bool) :=
  pairInduced_killsWeightedCoefficients D Sc cut 8 i j
    (weightedRestriction D Sc cut 8 M) (weightedRestriction_kills D Sc cut 8 M)

example (i j : Bool) := (pairWeightedModuleIso D Sc cut 8 i j M).hom_inv_id
example (i j : Bool) := (pairWeightedModuleIso D Sc cut 8 i j M).inv_hom_id
example (i j : Bool) := pairWeightedModuleIso_hom_mem D Sc cut 8 i j M
example (i j : Bool) := pairWeightedModuleIso_inv_mem D Sc cut 8 i j M

/-- Arbitrary old output arrows and input vectors use the prescribed forward map. -/
example (i j : Bool) (w : OldCategory D Sc cut)
    (g : (J i ⋙ J j).obj s ⟶ w) (b : M.obj (Q.obj s)) :=
  pairWeightedModuleIso_hom_tensor D Sc cut 8 i j M s w g b

example (i j : Bool) (w : OldCategory D Sc cut) (g : (J i ⋙ J j).obj s ⟶ w) :=
  pairWeightedModuleIso_hom_tensor D Sc cut 8 i j M s w g (𝟙 (Q.obj s))

private abbrev vacuum : OldCategory D Sc cut := ⟨[]⟩
private def vacuumModule : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj vacuum)

example (i j : Bool) :=
  pairWeightedModuleIso_hom_tensor D Sc cut 8 i j vacuumModule vacuum
    ((J i ⋙ J j).obj vacuum) (𝟙 _) (𝟙 (Q.obj vacuum))
end WeightedPairAppendConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPairAppend
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
