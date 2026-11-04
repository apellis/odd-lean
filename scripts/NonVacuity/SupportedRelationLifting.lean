import OddMath.QuiverHecke.SwappedAssembly.SupportedRelationLifting
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.CyclotomicAction
open OddMath.QuiverHecke.SwappedAssembly ProbeReservoir
namespace SupportedRelationLiftingConsumer
local instance homPi (A B : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
private abbrev D := WeightedAppendFixture.datum
private abbrev Sc := WeightedAppendFixture.scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private def cutoff : Bool → ℕ := fun _ => 4
private def ΛP : Bool → ℤ := fun i => probeCutoff D m i
private def ΛR : Bool → ℤ := fun _ => 4
private theorem hP (i : Bool) : (probeCutoff D m i : ℤ) = D.h i ΛP := rfl
private theorem hR (i : Bool) : (cutoff i : ℤ) = D.h i ΛR := rfl
private abbrev P := elvProbeReservoir D Sc m cutoff 12 ΛP ΛR hP hR
private abbrev H (t : Sector Bool) :=
  SupportedSectors.H D (parameterTwist D Sc) m cutoff 12 ΛP ΛR t

-- Every finite native word, with both moving parities, preserves exact support.
example {w : List (Col Bool (Bool → ℤ))} {s t : Sector Bool}
    (p : SPath w s t) (Z : H t) :
    SupportedSectors.retainedInput D Sc m cutoff 12 ΛP ΛR hP hR s
      ((P.pathFunctor p).obj Z.obj) :=
  SupportedSectors.retainedInput_path D Sc m cutoff 12 ΛP ΛR hP hR p Z.obj Z.property

-- The reduction accepts the actual supported rightmost families and arbitrary contexts.
example (Gs Ys : ∀ s, H s) (gens : P.Generators)
    (a b u : Obj (SKM.sig D)) (v : List (SKM.sig D).Colour) (hw : a.WhiskerOK u v) :
    (P.layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj) gens).toLocal.evalW
      (a.whisker u v) (b.whisker u v) u v (0 : LinDiagram ℚ a b) = 0 :=
  evalW_eq_zero_of_compEval_wt_on
    (SupportedSectors.retainedInput D Sc m cutoff 12 ΛP ΛR hP hR)
    (SupportedSectors.retainedInput_path D Sc m cutoff 12 ΛP ΛR hP hR)
    (fun s => (Ys s).property) gens _ (fun _ _ _ _ _ => Finsupp.sum_zero_index) u v hw

example (Gs Ys : ∀ s, H s) (gens : P.Generators) (r : SKM.Rel D)
    (h : ∀ {s t : Sector Bool} (p : SPath ((SKM.pres D Sc).dom r).word s t)
      (q : SPath ((SKM.pres D Sc).cod r).word s t) (Z : H t),
      P.wt t = ((SKM.pres D Sc).dom r).endR →
      compEval gens ((SKM.pres D Sc).rel r) p q Z.obj = 0) :
    RelHolds Sc (P.layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj) gens) r :=
  SupportedSectors.relHolds_of_supported_compEval D Sc m cutoff 12 ΛP ΛR hP hR Gs Ys gens r h
end SupportedRelationLiftingConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.SwappedAssembly.SupportedWhiskerReduction,
      `OddMath.QuiverHecke.SwappedAssembly.SupportedRelationLifting] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned declarations"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}: standard axioms only"
