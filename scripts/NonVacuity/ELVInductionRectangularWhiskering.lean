import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularWhiskering
import OddMath.QuiverHecke.CyclotomicAction.ELVOldMulticolourBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace RectangularWhiskeringConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 12
private abbrev A (i : Bool) := append D Sc cut i
private def N := oldRepresentable D Sc cut (⟨[false,true]⟩ : OldCategory D Sc cut)

/-- Actual mixed pair crossings on the occupied OLD representable. -/
example (i j l : Bool) := inductionComp_inner_transform
  (A i ⋙ A j) (A j ⋙ A i) (A l)
  (Distinct.cross_supernatural D Sc cut j i) N
example (i j l : Bool) := inductionComp_outer_transform (A i) (A j ⋙ A l) (A l ⋙ A j)
  (Distinct.cross_supernatural D Sc cut l j) N
example := inductionComp_inner_transform
  (append CyclotomicAction.AsymmetricParameters.datum CyclotomicAction.AsymmetricParameters.scalars cut true ⋙
    append CyclotomicAction.AsymmetricParameters.datum CyclotomicAction.AsymmetricParameters.scalars cut false)
  (append CyclotomicAction.AsymmetricParameters.datum CyclotomicAction.AsymmetricParameters.scalars cut false ⋙
    append CyclotomicAction.AsymmetricParameters.datum CyclotomicAction.AsymmetricParameters.scalars cut true)
  (append CyclotomicAction.AsymmetricParameters.datum CyclotomicAction.AsymmetricParameters.scalars cut true)
  (Distinct.cross_supernatural CyclotomicAction.AsymmetricParameters.datum
    CyclotomicAction.AsymmetricParameters.scalars cut false true)
  (oldRepresentable CyclotomicAction.AsymmetricParameters.datum
    CyclotomicAction.AsymmetricParameters.scalars cut ⟨[false,true]⟩)

private def R (ν : List Bool) :=
  (restriction (oldContentInclusion D Sc cut ν)).obj
    (oldRepresentable D Sc cut (⟨ν⟩ : OldCategory D Sc cut))
private abbrev J (ν : List Bool) (i : Bool) := oldContentAppend D Sc cut ν i

/-- Four distinct content categories on both moving parities. -/
example (i : Bool) := inductionComp_inner_transform
  (J [false,true] i ⋙ J (i :: [false,true]) i)
  (J [false,true] i ⋙ J (i :: [false,true]) i)
  (J (i :: i :: [false,true]) i)
  (oldContentMatrixCross_supernatural D Sc cut [false,true] i) (R [false,true])
example (i : Bool) := inductionComp_outer_transform
  (J [false,true] i)
  (J (i :: [false,true]) i ⋙ J (i :: i :: [false,true]) i)
  (J (i :: [false,true]) i ⋙ J (i :: i :: [false,true]) i)
  (oldContentMatrixCross_supernatural D Sc cut (i :: [false,true]) i) (R [false,true])
example (i : Bool) : probeOldVacuumAppendVector D Sc (fun _ => 5) i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc (fun _ => 5) i (by decide)
end RectangularWhiskeringConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularWhiskering
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
