import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCrossingComparison
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightCrossingComparisonExamples

private abbrev D := AsymmetricParameters.datum
private abbrev Sc := AsymmetricParameters.scalars
private abbrev X := Bool → ℤ
private def vacuumBlock : WeightBlocks D (0 : X) 0 := ⟨0, by simp⟩
private theorem step (i : Bool) : (0 : X) + D.α i = D.α i := zero_add _
private theorem step₂ (i j : Bool) : D.α j + D.α i = D.α j + D.α i := rfl
private theorem step₄ (i j : Bool) : D.α i + D.α j = D.α j + D.α i := add_comm _ _

private def sourceVacuum : ELVWeightProduct D Sc (fun _ => 12) 12 (0 : X) 0 :=
  fun β => if hb : β.1 = 0 then
    (by rw [hb]; exact vacuumModule D Sc (fun _ => 12) 12)
  else elvZeroModule D Sc (fun _ => 12) 12 β.1

/-- Stored intermediate content agrees with the independent canonical pair,
including repeated odd colours. -/
example (i j : Bool) := elvBlockPairCanonical_eq D Sc (fun _ => 12) 12 i j (0 : X)
  (step j) (step₂ i j) vacuumBlock

example (i j : Bool) := elvBlockPairComparison_hom D Sc (fun _ => 12) 12 i j (0 : X)
  (step j) (step₂ i j) vacuumBlock

example (i j : Bool) := elvBlockPairComparison_inv D Sc (fun _ => 12) 12 i j (0 : X)
  (step j) (step₂ i j) vacuumBlock

/-- The original product-induction coordinate agrees with the independent
canonical content pair on the actual vacuum family. -/
example (i j : Bool) := Functor.congr_obj
  (elvEFunctor_comp₂_contentPair_eq D Sc (fun _ => 12) 12 i j (0 : X)
    (step j) (step₂ i j) vacuumBlock _ rfl) sourceVacuum

/-- The whole comparison commutes with that endpoint equality, for both
directions and without expanding the product-induction component casts. -/
example (i j : Bool) := elvWeightPairComparison_eq D Sc (fun _ => 12) 12 i j (0 : X)
  (step j) (step₂ i j) vacuumBlock _ rfl

/-- The twisted parameter category has the same chosen crossing comparison. -/
example := elvBlockPairComparison_hom D (parameterTwist D Sc) (fun _ => 12) 12
  true false (0 : X) (step false) (step₂ true false) vacuumBlock

end OddMath.QuiverHecke.ELVWeightCrossingComparisonExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightCrossingComparison
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
