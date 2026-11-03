import OddMath.QuiverHecke.CyclotomicAction.ELVMatrixEntryNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeShiftedCapComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace ProbeShiftedCapComparisonConsumer
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


/-- The selected source comparison uses the prescribed ordinary counit. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeMappedAppendLinear_capDotRow D Sc m ν i (N1 i) (hN1 i) w 0

/-- Both moving parities and every actual dotted cap row on the mixed regular module. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (n : ℕ) :=
  probeMappedAppendLinear_shiftedCapRow D Sc m ν i (N1 i) (hN1 i) w n

private def M0 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private def N0 := probeOldModule D m Sc [] M0
private abbrev hN0 := probeOldModule_evaluatesCoefficients D m Sc [] M0
private def O0 := probeOrdinaryModuleSuperfunctor D Sc m [] N0 hN0
private abbrev s0 : ELVOld.OldContentCategory D Sc cut [] :=
  ELVOld.oldContentObject D Sc cut [] ⟨[],List.Perm.refl []⟩

private def M01 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 1)
private def N01 (i : Bool) := probeOldModule D m Sc [i] M01

private abbrev hN01 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc [i] M01
private def O01 (i : Bool) := probeOrdinaryModuleSuperfunctor D Sc m [i] (N01 i) (hN01 i)

/-- Vacuum includes every power of the original odd dot and the chosen counit. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut [i]) (n : ℕ) :=
  probeMappedAppendLinear_shiftedCapRow D Sc m [] i (N01 i) (hN01 i) w n

example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut [i]) :=
  probeMappedAppendLinear_capDotRow D Sc m [] i (N01 i) (hN01 i) w 0

/-- The raw shifted maps are the total components of the given module rows. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (n : ℕ) :=
  shiftedCapDotRow_total (J ν i) (probeOldContentAppendDot_supernatural D Sc m ν i)
    (N1 i) n w

example (i : Bool) (w : OrdinaryContentCategory D Sc a (i :: ν)) (n : ℕ) :=
  shiftedCapDotRow_total (T ν i) (probeOrdinaryAppendDot_supernatural D Sc m ν i)
    (O1 i) n w

example (i : Bool) (n : ℕ) :=
  shiftedCapDotRow_mem (J ν i) (probeOldContentAppendDot_supernatural D Sc m ν i) (N1 i) n

example (i : Bool) (n : ℕ) :=
  shiftedCapDotRow_mem (T ν i) (probeOrdinaryAppendDot_supernatural D Sc m ν i) (O1 i) n

/-- The old normalized kernel field is retained literally, also for old
representables, which need no scalar-evaluation hypothesis. -/
example (i : Bool) (s : ELVOld.OldCategory D Sc cut) (b : ℕ) (r : Fin b) :=
  ELVOld.CyclotomicCrossingTensor.capMatrixEntry_some_eq_shiftedCapDotRow D Sc cut i
    (ELVOld.oldRepresentable D Sc cut s) b r

end ProbeShiftedCapComparisonConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeShiftedCapComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
