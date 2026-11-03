import OddMath.QuiverHecke.CyclotomicAction.ELVOldNestedBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OldNestedBraidConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 6
private abbrev J (i : Bool) := append D Sc cut i
private def source (v : List Bool) : OldCategory D Sc cut := ⟨v⟩
private def R (v : List Bool) := oldRepresentable D Sc cut (source v)
private abbrev value (v : List Bool) (i : Bool) :=
  induced (J i) (induced (J i) (induced (J i) (R v)))
private abbrev upper (v : List Bool) (i : Bool) :=
  (J i).obj ((J i).obj ((J i).obj (source v)))
private def vector (v : List Bool) (i : Bool) : (value v i).obj (upper v i) :=
  tensor (J i) (induced (J i) (induced (J i) (R v))).toFunctor
    ((J i).obj ((J i).obj (source v))) (𝟙 _)
    (tensor (J i) (induced (J i) (R v)).toFunctor ((J i).obj (source v)) (𝟙 _)
      (tensor (J i) (R v).toFunctor (source v) (𝟙 _) (𝟙 (source v))))

example (i : Bool) := oldTripleFlattening_prefix_cross D Sc cut i (R [false,true])
example (i : Bool) := oldTripleFlattening_suffix_cross D Sc cut i (R [false,true])
example (i : Bool) := oldNestedCross_braid D Sc cut i (R [])
example (i : Bool) := signedOldNestedCross_braid D Sc cut i (R [false,true])
example (i : Bool) := signedOldNestedCross_braid D Sc cut i (supermoduleParityObj (R []))

/-- The prescribed negative braid on the literal threefold unit tensor. -/
example (i : Bool) := congrArg
  (fun f : End (value [false,true] i) => f.total (upper [false,true] i) (vector [false,true] i))
  (signedOldNestedCross_braid D Sc cut i (R [false,true]))
end OldNestedBraidConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOldNestedBraid
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
