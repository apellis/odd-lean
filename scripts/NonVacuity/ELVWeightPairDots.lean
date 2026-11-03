import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairDots
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightPairDotsExamples

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

/-- Both independently assembled weight dots agree with the supported
content steps, for arbitrary moving colours including repetition. -/
example (i j : Bool) (p : ZMod 2) :=
  elvWeightInnerDot_blockSucc D Sc (fun _ => 12) 12 i j (0 : X)
    (step j) (step₂ i j) p vacuumBlock sourceVacuum

example (i j : Bool) (p : ZMod 2) :=
  elvWeightOuterDot_blockSucc D Sc (fun _ => 12) 12 i j (0 : X)
    (step j) (step₂ i j) p vacuumBlock sourceVacuum

/-- The actual pair coordinates retain the independent single-letter dots. -/
example (i j : Bool) :=
  elvWeightInnerDot_contentPair D Sc (fun _ => 12) 12 i j (0 : X)
    (step j) (step₂ i j) vacuumBlock sourceVacuum

example (i j : Bool) :=
  elvWeightOuterDot_contentPair D Sc (fun _ => 12) 12 i j (0 : X)
    (step j) (step₂ i j) vacuumBlock sourceVacuum

/-- Recasting the stored intermediate content preserves each actual dot. -/
example (i j : Bool) := contentPairInnerDotTo_eq D Sc (fun _ => 12) 12 i j
  0 ([i] : Multiset Bool) ([i,j] : Multiset Bool) (zero_add _)
  (by rfl) (zero_add _) (vacuumModule D Sc (fun _ => 12) 12)

example (i j : Bool) := contentPairOuterDotTo_eq D Sc (fun _ => 12) 12 i j
  0 ([i] : Multiset Bool) ([i,j] : Multiset Bool) (zero_add _)
  (by rfl) (zero_add _) (vacuumModule D Sc (fun _ => 12) 12)

end OddMath.QuiverHecke.ELVWeightPairDotsExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairDots
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
