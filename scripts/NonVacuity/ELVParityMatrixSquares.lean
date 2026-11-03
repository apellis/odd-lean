import OddMath.QuiverHecke.CyclotomicAction.ELVParityMatrixSquares
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace ParityMatrixSquaresConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private abbrev ν : List Bool := [false,true]
private def M := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 2)
private def N := probeOldModule D m Sc ν M
private abbrev hN := probeOldModule_evaluatesCoefficients D m Sc ν M
private def O := probeOrdinaryModuleSuperfunctor D Sc m ν N hN
private abbrev J (μ : List Bool) (i : Bool) := ELVOld.oldContentAppend D Sc cut μ i
private abbrev T (μ : List Bool) (i : Bool) := probeOrdinaryAppend D Sc m μ i
private abbrev Q (μ : List Bool) := probeOldOrdinaryFunctor D Sc m μ
private abbrev h (μ : List Bool) (i : Bool) := probeOldOrdinaryFunctor_append D Sc m μ i

private def M1 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 3)
private def N1 (i : Bool) := probeOldModule D m Sc (i :: ν) M1
private abbrev hN1 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc (i :: ν) M1
private def O1 (i : Bool) := probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) (N1 i) (hN1 i)



private def oldL (i : Bool) := induced (J ν i) N
private def newL (i : Bool) := (induction (T ν i)).obj O
private def chart (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :
    (oldL i).obj w ≃ₗ[ℚ] (newL i).obj ((Q (i :: ν)).obj w) :=
  probeAppendLinearEquiv D Sc m ν N hN i w
private def oldPower (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (n : ℕ) :
    Module.End ℚ ((oldL i).obj w) := (probeOldContentInductionDot D Sc m ν i N w) ^ n
private def newPower (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (n : ℕ) :
    Module.End ℚ ((newL i).obj ((Q (i :: ν)).obj w)) :=
  (transformLinear (probeOrdinaryAppendDot_supernatural D Sc m ν i) O ((Q (i :: ν)).obj w)) ^ n

private theorem plainSquare (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (n : ℕ) :
    (chart i w).toLinearMap ∘ₗ oldPower i w n = newPower i w n ∘ₗ (chart i w).toLinearMap :=
  linearSquare_reencode _ _ _ _ _ _ _ _
    (probeAppendLinearEquiv_hom D Sc m ν N hN i w) rfl rfl
    (probeAppendLinearEquiv_hom D Sc m ν N hN i w)
    (probeAppendComparisonLinear_dot_pow D Sc m ν N hN i w n)

private abbrev oldPi (i : Bool) : PiSupercategory ℚ
    (Superfunctor ℚ (ELVOld.OldContentCategory D Sc cut (i :: ν)) (SVec ℚ)) :=
  ELVOld.supermodulePiSupercategory
private abbrev newPi (i : Bool) : PiSupercategory ℚ
    (Superfunctor ℚ (OrdinaryContentCategory D Sc a (i :: ν)) (SVec ℚ)) :=
  ELVOld.supermodulePiSupercategory
attribute [local instance] oldPi newPi

private def oldSource (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2) :=
  (ELVOld.moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := ℚ) q).iso (oldL i)) w).toLinearMap
private def newSource (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2) :=
  (ELVOld.moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := ℚ) q).iso (newL i)) ((Q (i :: ν)).obj w)).toLinearMap
private def oldTarget (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2) :=
  (ELVOld.moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := ℚ) q).iso (oldL i)) w).symm.toLinearMap
private def newTarget (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2) :=
  (ELVOld.moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := ℚ) q).iso (newL i)) ((Q (i :: ν)).obj w)).symm.toLinearMap
private def shiftedChart (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2) :=
  shiftedModuleValueLinearEquiv (oldL i) (newL i) w ((Q (i :: ν)).obj w) (chart i w) q

/-- Actual selected append charts and signed dot powers, both colours, all source shifts. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (n : ℕ) (q : ZMod 2) :=
  linearColumn_parity_square (chart i w).toLinearMap (oldPower i w n) (newPower i w n)
    (chart i w).toLinearMap (oldSource i w q) (newSource i w q) (shiftedChart i w q).toLinearMap
    (oldPower i w n ∘ₗ oldSource i w q) (newPower i w n ∘ₗ newSource i w q)
    (plainSquare i w n)
    (shiftedModuleValueLinearEquiv_source_square (oldL i) (newL i) w ((Q (i :: ν)).obj w) (chart i w) q)
    rfl rfl

/-- The same actual signed powers and selected chart with canonical target shifts. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (n : ℕ) (q : ZMod 2) :=
  linearRow_parity_square (chart i w).toLinearMap (oldPower i w n) (newPower i w n)
    (chart i w).toLinearMap (oldTarget i w q) (newTarget i w q) (shiftedChart i w q).toLinearMap
    (oldTarget i w q ∘ₗ oldPower i w n) (newTarget i w q ∘ₗ newPower i w n)
    (plainSquare i w n)
    (shiftedModuleValueLinearEquiv_target_square (oldL i) (newL i) w ((Q (i :: ν)).obj w) (chart i w) q)
    rfl rfl

/-- The exact canonical coordinates used by both signed-power squares. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2) :=
  shiftedModuleValueLinearEquiv_source_square (oldL i) (newL i) w ((Q (i :: ν)).obj w) (chart i w) q
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2) :=
  shiftedModuleValueLinearEquiv_target_square (oldL i) (newL i) w ((Q (i :: ν)).obj w) (chart i w) q

private def M0 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private def N0 := probeOldModule D m Sc [] M0
private abbrev hN0 := probeOldModule_evaluatesCoefficients D m Sc [] M0

/-- Vacuum uses the same actual module parity coordinates on the chosen append chart. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut [i]) (q : ZMod 2) :=
  shiftedModuleValueLinearEquiv_source_square (induced (J [] i) N0)
    ((induction (T [] i)).obj (probeOrdinaryModuleSuperfunctor D Sc m [] N0 hN0))
    w ((Q [i]).obj w) (probeAppendLinearEquiv D Sc m [] N0 hN0 i w) q

end ParityMatrixSquaresConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVParityMatrixSquares
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
