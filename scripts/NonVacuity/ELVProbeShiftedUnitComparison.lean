import OddMath.QuiverHecke.CyclotomicAction.ELVProbeShiftedUnitComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace ProbeShiftedUnitComparisonConsumer
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


/-- Both moving parities, all actual unit/dot columns, with no rescaling. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut ν) (n : ℕ) :=
  probeAppendComparisonLinear_unitDotColumn D Sc m ν N hN i w n

/-- The full canonical module source coordinate commutes with the selected chart. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut ν) (n : ℕ) :=
  probeAppendComparisonLinear_shiftedUnitColumn D Sc m ν N hN i w n

example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeAppendComparisonLinear_dot D Sc m ν N hN i w

example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (n : ℕ) :=
  probeAppendComparisonLinear_dot_pow D Sc m ν N hN i w n

/-- These raw maps are components of the actual shifted module columns. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut ν) (n : ℕ) :=
  shiftedUnitDotColumn_total (J ν i) (probeOldContentAppendDot_supernatural D Sc m ν i) N n w

example (i : Bool) (w : OrdinaryContentCategory D Sc a ν) (n : ℕ) :=
  shiftedUnitDotColumn_total (T ν i) (probeOrdinaryAppendDot_supernatural D Sc m ν i) O n w

example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut ν) (n : ℕ) :=
  endpointShiftedUnitDotLinear_total (T ν i) (probeOrdinaryAppendDot_supernatural D Sc m ν i)
    O n ((Q ν).obj w) ((Q (i :: ν)).obj ((J ν i).obj w)) rfl

example (i : Bool) (n : ℕ) :=
  shiftedUnitDotColumn_mem (J ν i) (probeOldContentAppendDot_supernatural D Sc m ν i) N n

example (i : Bool) (n : ℕ) :=
  shiftedUnitDotColumn_mem (T ν i) (probeOrdinaryAppendDot_supernatural D Sc m ν i) O n

private def M0 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private def N0 := probeOldModule D m Sc [] M0
private abbrev hN0 := probeOldModule_evaluatesCoefficients D m Sc [] M0
private abbrev s0 : ELVOld.OldContentCategory D Sc cut [] :=
  ELVOld.oldContentObject D Sc cut [] ⟨[],List.Perm.refl []⟩

/-- Vacuum checks every signed dot power and both canonical source shifts. -/
example (i : Bool) (n : ℕ) :=
  probeAppendComparisonLinear_unitDotColumn D Sc m [] N0 hN0 i s0 n

example (i : Bool) (n : ℕ) :=
  probeAppendComparisonLinear_shiftedUnitColumn D Sc m [] N0 hN0 i s0 n

/-- The actual old finite unit field, including non-scalar old representables. -/
example (i : Bool) (s : ELVOld.OldCategory D Sc cut) (b : ℕ) (r : Fin b) :=
  ELVOld.CyclotomicCrossingTensor.unitMatrixEntry_some_eq_shiftedUnitDotColumn D Sc cut i
    (ELVOld.oldRepresentable D Sc cut s) b r

end ProbeShiftedUnitComparisonConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeShiftedUnitComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
