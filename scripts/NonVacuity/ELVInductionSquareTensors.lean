import OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld
namespace InductionSquareTensorsConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M : Superfunctor ℚ (TruncatedCategory D Sc cut 8) (SVec ℚ) :=
  WeightedAppendFixture.truncatedRepresentable D Sc cut 8 (Q.obj s)
private def R : Superfunctor ℚ (OldCategory D Sc cut) (SVec ℚ) := weightedRestriction D Sc cut 8 M
private def c : (BalancedInduction.induction Q).obj R ⟶ M :=
  (quotientInductionCounitIso D Sc cut 8 M).hom
private theorem c_even : c ∈ parity (R := ℚ) _ _ 0 :=
  quotientInductionCounitIso_hom_mem D Sc cut 8 M
private abbrev J (i : Bool) := CyclotomicCrossingTensor.append D Sc cut i
private abbrev T (i : Bool) := truncatedAppend D Sc cut 8 [i]

example (i : Bool) (w : OldCategory D Sc cut) (g : (J i).obj s ⟶ w)
    (b : R.obj s) :
    (BalancedInduction.squareComparison (J i) Q Q (T i)
      (oldAppend_truncate D Sc cut 8 i) R M
      c).total (Q.obj w)
      (BalancedInduction.tensor Q ((BalancedInduction.induction (J i)).obj R).toFunctor
        w (𝟙 (Q.obj w)) (BalancedInduction.tensor (J i) R.toFunctor s g b)) =
      BalancedInduction.tensor (T i) M.toFunctor (Q.obj s)
        (eqToHom (congrArg
          (fun H : OldCategory D Sc cut ⥤ TruncatedCategory D Sc cut 8 => H.obj s)
          (oldAppend_truncate D Sc cut 8 i)).symm ≫ Q.map g)
        (SuperNatTrans.app c 0 (Q.obj s) (BalancedInduction.unit Q R.toFunctor s b)) :=
   BalancedInduction.squareComparison_total_tensor (J i) Q Q (T i)
    (oldAppend_truncate D Sc cut 8 i) R M
    c
    c_even s w g b

example (i : Bool) :
    BalancedInduction.squareComparison (J i) Q Q (T i)
      (oldAppend_truncate D Sc cut 8 i) R M c ∈
      parity (R := ℚ) ((BalancedInduction.induction (J i) ⋙ BalancedInduction.induction Q).obj R)
        ((BalancedInduction.induction (T i)).obj M) 0 :=
  BalancedInduction.squareComparison_mem (J i) Q Q (T i)
    (oldAppend_truncate D Sc cut 8 i) R M c c_even

/-- The same chosen square computes directly on the literal old coends. -/
example (i : Bool) (w : OldCategory D Sc cut) (g : (J i).obj s ⟶ w)
    (b : R.obj s) :
    BalancedInduction.squareLinear (J i) Q Q (T i)
      (oldAppend_truncate D Sc cut 8 i) R M c (Q.obj w)
      (BalancedInduction.tensor Q (BalancedInduction.induced (J i) R).toFunctor
        w (𝟙 (Q.obj w)) (BalancedInduction.tensor (J i) R.toFunctor s g b)) =
      BalancedInduction.tensor (T i) M.toFunctor (Q.obj s)
        (eqToHom (congrArg
          (fun H : OldCategory D Sc cut ⥤ TruncatedCategory D Sc cut 8 => H.obj s)
          (oldAppend_truncate D Sc cut 8 i)).symm ≫ Q.map g)
        (SuperNatTrans.app c 0 (Q.obj s) (BalancedInduction.unit Q R.toFunctor s b)) :=
  BalancedInduction.squareLinear_tensor (J i) Q Q (T i)
    (oldAppend_truncate D Sc cut 8 i) R M c c_even s w g b
end InductionSquareTensorsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareTensors
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
