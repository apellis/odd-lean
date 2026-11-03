import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMateNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace InductionGridMateNaturalityConsumer
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

private def M01 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 1)
private def N01 (i : Bool) := probeOldModule D m Sc [i] M01

local instance gridMateNaturalityOldPi (i : Bool) : PiSupercategory ℚ
    (Superfunctor ℚ (ELVOld.OldContentCategory D Sc cut (i :: ν)) (SVec ℚ)) := supermodulePiSupercategory
local instance gridMateNaturalityOrdinaryPi (i : Bool) : PiSupercategory ℚ
    (Superfunctor ℚ (OrdinaryContentCategory D Sc a (i :: ν)) (SVec ℚ)) := supermodulePiSupercategory
/-- The actual signed mate families, on both moving parities. -/
example (i : Bool) := orderedGridMateComponent_supernatural (J ν i) (J (i :: ν) i)
  (probeOldContentEqualCross_supernatural D Sc m ν i)
example (i : Bool) := orderedGridMateComponent_supernatural (T ν i) (T (i :: ν) i)
  (probeOrdinaryEqualCross_supernatural D Sc m ν i)
example (i : Bool) := gridDoubleCrossComponent_supernatural (J ν i) (J (i :: ν) i)
  (probeOldContentEqualCross_supernatural D Sc m ν i)
example (i : Bool) := gridDoubleCrossComponent_supernatural (T ν i) (T (i :: ν) i)
  (probeOrdinaryEqualCross_supernatural D Sc m ν i)
/-- Apply the input naturality law to the actual ODD canonical parity map;
its homogeneity hypothesis is proved, not assumed. -/
example (i : Bool) :=
  (orderedGridMateComponent_supernatural (J ν i) (J (i :: ν) i)
    (probeOldContentEqualCross_supernatural D Sc m ν i)).naturality
      ((SKM.homParityShiftDatum (k := ℚ) 1).hom_mem (N1 i))
example (i : Bool) :=
  (orderedGridMateComponent_supernatural (T ν i) (T (i :: ν) i)
    (probeOrdinaryEqualCross_supernatural D Sc m ν i)).naturality
      ((SKM.homParityShiftDatum (k := ℚ) 1).hom_mem (O1 i))
/-- Empty predecessor/output[i], with both actual successive adjunctions. -/
example (i : Bool) := orderedGridMateComponent_supernatural (J [] i) (J [i] i)
  (probeOldContentEqualCross_supernatural D Sc m [] i)
example (i : Bool) := orderedGridMateComponent_supernatural (T [] i) (T [i] i)
  (probeOrdinaryEqualCross_supernatural D Sc m [] i)

end InductionGridMateNaturalityConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMateNaturality
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
