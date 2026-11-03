import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularTriple
import OddMath.QuiverHecke.CyclotomicAction.ELVOldMulticolourBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentAppendTo
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace RectangularTripleConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 12
private abbrev A (i : Bool) := append D Sc cut i
private def N := oldRepresentable D Sc cut (⟨[false,true]⟩ : OldCategory D Sc cut)

/-- The independently defined rectangular prefix and suffix on mixed triples. -/
example (i j l : Bool) := inductionTripleFlattening_prefix_rectangular
  (A i) (A j) (A j) (A i) (A l)
  (Distinct.cross_supernatural D Sc cut i j) N
example (i j l : Bool) := inductionTripleFlattening_suffix_rectangular
  (A i) (A j) (A l) (A l) (A j)
  (Distinct.cross_supernatural D Sc cut j l) N
example := inductionTripleFlattening_prefix_rectangular
  (append CyclotomicAction.AsymmetricParameters.datum CyclotomicAction.AsymmetricParameters.scalars cut true)
  (append CyclotomicAction.AsymmetricParameters.datum CyclotomicAction.AsymmetricParameters.scalars cut false)
  (append CyclotomicAction.AsymmetricParameters.datum CyclotomicAction.AsymmetricParameters.scalars cut false)
  (append CyclotomicAction.AsymmetricParameters.datum CyclotomicAction.AsymmetricParameters.scalars cut true)
  (append CyclotomicAction.AsymmetricParameters.datum CyclotomicAction.AsymmetricParameters.scalars cut true)
  (Distinct.cross_supernatural CyclotomicAction.AsymmetricParameters.datum
    CyclotomicAction.AsymmetricParameters.scalars cut true false)
  (oldRepresentable CyclotomicAction.AsymmetricParameters.datum
    CyclotomicAction.AsymmetricParameters.scalars cut ⟨[false,true]⟩)

private def R (ν : List Bool) :=
  (restriction (oldContentInclusion D Sc cut ν)).obj
    (oldRepresentable D Sc cut (⟨ν⟩ : OldCategory D Sc cut))
private abbrev J (ν : List Bool) (i : Bool) := oldContentAppend D Sc cut ν i

/-- The triple comparisons retain four changing content categories. -/
example (i : Bool) := inductionTripleFlattening_prefix_rectangular
  (J [false,true] i) (J (i :: [false,true]) i)
  (J [false,true] i) (J (i :: [false,true]) i)
  (J (i :: i :: [false,true]) i)
  (oldContentMatrixCross_supernatural D Sc cut [false,true] i) (R [false,true])
example (i : Bool) := inductionTripleFlattening_suffix_rectangular
  (J [false,true] i)
  (J (i :: [false,true]) i) (J (i :: i :: [false,true]) i)
  (J (i :: [false,true]) i) (J (i :: i :: [false,true]) i)
  (oldContentMatrixCross_supernatural D Sc cut (i :: [false,true]) i) (R [false,true])
private abbrev ν : List Bool := [false,true]
private abbrev swappedUpper (i j : Bool) := oldContentAppendTo D Sc cut (j :: ν) i
  (j :: i :: ν) (List.Perm.swap j i ν)
private theorem mixedCross (i j : Bool) :
    IsSupernatural ℚ (D.parity i * D.parity j)
      (F := J ν j ⋙ swappedUpper i j) (G := J ν i ⋙ J (i :: ν) j)
      (fun s => Distinct.crossComponent D Sc cut i j s.obj) where
  mem s := (Distinct.cross_supernatural D Sc cut i j).mem s.obj
  naturality hf := (Distinct.cross_supernatural D Sc cut i j).naturality hf

/-- Distinct colours use different middle content categories and a literal shared upper target. -/
example (i j l : Bool) := inductionTripleFlattening_prefix_rectangular
  (J ν i) (J (i :: ν) j) (J ν j) (swappedUpper i j)
  (J (j :: i :: ν) l) (mixedCross i j) (R ν)

example (i : Bool) : probeOldVacuumAppendVector D Sc (fun _ => 5) i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero D Sc (fun _ => 5) i (by decide)
end RectangularTripleConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularTriple
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
