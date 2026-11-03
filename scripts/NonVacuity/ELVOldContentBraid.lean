import OddMath.QuiverHecke.CyclotomicAction.ELVOldContentBraid
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
namespace OldContentBraidConsumer
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 6
private def R (ν : List Bool) :=
  (restriction (oldContentInclusion D Sc cut ν)).obj
    (oldRepresentable D Sc cut (⟨ν⟩ : OldCategory D Sc cut))

private abbrev J (ν : List Bool) (i : Bool) := oldContentAppend D Sc cut ν i
private def source (ν : List Bool) : OldContentCategory D Sc cut ν :=
  ⟨⟨ν⟩, List.Perm.refl _⟩
private abbrev value (ν : List Bool) (i : Bool) :=
  induced (J (i :: i :: ν) i) (induced (J (i :: ν) i) (induced (J ν i) (R ν)))
private abbrev upper (ν : List Bool) (i : Bool) :=
  (J (i :: i :: ν) i).obj ((J (i :: ν) i).obj ((J ν i).obj (source ν)))
private def vector (ν : List Bool) (i : Bool) : (value ν i).obj (upper ν i) :=
  tensor (J (i :: i :: ν) i) (induced (J (i :: ν) i) (induced (J ν i) (R ν))).toFunctor
    ((J (i :: ν) i).obj ((J ν i).obj (source ν))) (𝟙 _)
    (tensor (J (i :: ν) i) (induced (J ν i) (R ν)).toFunctor
      ((J ν i).obj (source ν)) (𝟙 _)
      (tensor (J ν i) (R ν).toFunctor (source ν) (𝟙 _) (𝟙 (source ν).obj)))

/-- Both moving parities on empty and occupied mixed content, without a
supplied source braid or inverse. The three induction edges change category. -/
example (i : Bool) := oldContentInductionCross_braid D Sc cut [] i (R [])
example (i : Bool) := oldContentInductionCross_braid D Sc cut [false,true] i
  (R [false,true])
example (i : Bool) := oldContentInductionCross_braid D Sc cut [false,true] i
  (supermoduleParityObj (R [false,true]))

/-- The generic grid theorem is used with the proved literal quotient relation. -/
example (i : Bool) := gridDoubleCrossComponent_braid
  (oldContentAppend D Sc cut [] i)
  (oldContentAppend D Sc cut [i] i)
  (oldContentAppend D Sc cut [i,i] i)
  (oldContentMatrixCross_supernatural D Sc cut [] i)
  (oldContentMatrixCross_supernatural D Sc cut [i] i)
  (oldContentEqualCross_braid D Sc cut [] i) (R [])
/-- The equation applies to the literal nested unit tensor at mixed content. -/
example (i : Bool) := congrArg
  (fun f : End (value [false,true] i) => f.total (upper [false,true] i) (vector [false,true] i))
  (oldContentInductionCross_braid D Sc cut [false,true] i (R [false,true]))
end OldContentBraidConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridBraid,
      `OddMath.QuiverHecke.CyclotomicAction.ELVOldContentBraid] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
