import OddMath.QuiverHecke.CyclotomicAction.ELVSourcePowerComparison
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

/-! Literal powers and arbitrary odd coefficient generators in actual full
old ELV Homs, without identifying a power ideal with a weighted ideal.
-/
noncomputable section
namespace NonVacuity.ELVSourcePowerComparison
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sc := CyclotomicAction.AsymmetricParameters.scalars
private def T : Set (SKM.SYM D ℚ) :=
  {SKM.SYM.e D ℚ false 1, SKM.SYM.delta D ℚ ⟨true, rfl⟩}
private def L (_ : Bool × ℕ) : ℕ := 3

/-- The full source and actual target scalar spans agree for both parities. -/
example : (CoefficientGeneratorSpan D Sc T [false, true] [true, false]).map
    (elvQuotientMap D Sc (fun _ => 6) _ _) =
      coefficientGeneratorHomSpan D Sc (fun _ => 6)
        (SKM.SYM.elvCoefficientQuotient D (fun _ => 6) '' T) [false, true] [true, false] :=
  map_coefficientGeneratorSpan D Sc (fun _ => 6) T [false, true] [true, false]

/-- This pulls back the actual first-boundary ideal plus actual scalar spans. -/
example := comap_oldIdeal_sup_coefficientGenerators D Sc (fun _ => 6) T
  [false, true] [true, false]

/-- Literal elementary powers, at every word context, have exactly their
prescribed source presentation preimage. -/
example := comap_oldIdeal_sup_elementaryPowers D Sc (fun _ => 6) L
  [false, true] [true, false]

/-- These concrete powers satisfy a genuine lower weight bound of six. -/
example (a : Bool × ℕ) : 6 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 6 ≤ 3 * (2 * (a.2 + 1))
  omega

end NonVacuity.ELVSourcePowerComparison

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVSourcePowerComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
