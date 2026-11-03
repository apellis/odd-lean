import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexLocal
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
namespace ProbeReindexLocalConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 2 else 4
private theorem h₁ (ν : List Bool) (i : Bool) : (i :: ν).Perm (ν ++ [i]) :=
  (show ([i] ++ ν).Perm (ν ++ [i]) from List.perm_append_comm)
private theorem h₂ (ν : List Bool) (i : Bool) : (i :: (ν ++ [i])).Perm (ν ++ [i,i]) := by
  simpa only [List.append_assoc, List.singleton_append] using
    (show ([i] ++ (ν ++ [i])).Perm ((ν ++ [i]) ++ [i]) from List.perm_append_comm)
private def pos (i : Bool) := probeReindexInvPos D Sc m [i,i] i (h₁ [i,i] i) (h₂ [i,i] i)
  (by cases i <;> decide)
private def neg (i : Bool) := probeReindexInvNeg D Sc m [] i (h₁ [] i) (h₂ [] i)
  (by cases i <;> decide)
private abbrev mixed (i : Bool) : List Bool := [i,!i,i,i,i]
private def mixedPos (i : Bool) := probeReindexInvPos D Sc m (mixed i) i
  (h₁ (mixed i) i) (h₂ (mixed i) i) (by cases i <;> decide)
private def mixedNeg (i : Bool) := probeReindexInvNeg D Sc m [false,true] i
  (h₁ [false,true] i) (h₂ [false,true] i) (by cases i <;> decide)
example (i : Bool) := (pos i).total
example (i : Bool) := (neg i).total
example (i : Bool) := (mixedPos i).total
example (i : Bool) := (mixedNeg i).total
example (i : Bool) := (pos i).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) := (neg i).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
example (i : Bool) := (pos i).f'_mem
example (i : Bool) := (neg i).g'_mem 7
example (i : Bool) := probeReindexLowerLoopSuperIso_hom_mem D Sc m [false,true] i
  (h₁ [false,true] i)
example (i : Bool) := probeReindexUpperLoopSuperIso_hom_mem D Sc m [false,true] i
  (h₁ [false,true] i) (h₂ [false,true] i)
end ProbeReindexLocalConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexLocal
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
