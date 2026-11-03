import OddMath.QuiverHecke.CyclotomicAction.ELVInductionTripleDots
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixEntries
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace TripleDotsConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 12
private abbrev A (i : Bool) := append D Sc cut i
private def N := oldRepresentable D Sc cut (⟨[false,true]⟩ : OldCategory D Sc cut)
example (i j l : Bool) := inductionTripleFlattening_first_dot (A i) (A j) (A l)
  (oldAppendDot_supernatural D Sc cut i) N
example (i j l : Bool) := inductionTripleFlattening_middle_dot (A i) (A j) (A l)
  (oldAppendDot_supernatural D Sc cut j) N
example (i j l : Bool) := inductionTripleFlattening_last_dot (A i) (A j) (A l)
  (oldAppendDot_supernatural D Sc cut l) N
example (i j l : Bool) := inductionTripleFlattening_middle_dot (A i) (A j) (A l)
  (oldAppendDot_supernatural D Sc cut j) (supermoduleParityObj N)

private abbrev Dodd := CyclotomicAction.AsymmetricParameters.datum
private abbrev Sodd := CyclotomicAction.AsymmetricParameters.scalars
example := inductionTripleFlattening_last_dot (append Dodd Sodd cut true)
  (append Dodd Sodd cut false) (append Dodd Sodd cut true)
  (oldAppendDot_supernatural Dodd Sodd cut true) (oldRepresentable Dodd Sodd cut ⟨[true,false]⟩)

private abbrev ν : List Bool := [false,true]
private abbrev J (ν : List Bool) (i : Bool) := oldContentAppend D Sc cut ν i
private def R := (restriction (oldContentInclusion D Sc cut ν)).obj
  (oldRepresentable D Sc cut (⟨ν⟩ : OldCategory D Sc cut))
/-- All three dots retain four changing content categories, on both moving parities. -/
example (i j l : Bool) := inductionTripleFlattening_first_dot
  (J ν i) (J (i :: ν) j) (J (j :: i :: ν) l)
  (oldContentAppendDot_supernatural D Sc cut ν i) R
example (i j l : Bool) := inductionTripleFlattening_middle_dot
  (J ν i) (J (i :: ν) j) (J (j :: i :: ν) l)
  (oldContentAppendDot_supernatural D Sc cut (i :: ν) j) R
example (i j l : Bool) := inductionTripleFlattening_last_dot
  (J ν i) (J (i :: ν) j) (J (j :: i :: ν) l)
  (oldContentAppendDot_supernatural D Sc cut (j :: i :: ν) l) R
example (i : Bool) : probeOldVacuumAppendVector D Sc (fun _ => 5) i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc (fun _ => 5) i (by decide)
end TripleDotsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionTripleDots
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
