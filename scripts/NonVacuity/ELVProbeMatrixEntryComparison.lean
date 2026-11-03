import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixEntryComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace ProbeMatrixEntryComparisonConsumer
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


/-- Both moving parities of the literal same-colour crossing, with p²=p. -/
example (i : Bool) := probeMatrixOldCross_supernatural D Sc m ν i
example (i : Bool) := probeMatrixOrdinaryCross_supernatural D Sc m ν i

/-- The genuine selected E/F and F/E charts carry the prescribed mate. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeMatrixCharts_mate D Sc m ν i (N1 i) (hN1 i) w

/-- Original unit and signed dot/counit maps, for every power. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (n : ℕ) :=
  probeMatrixCharts_unitDotColumn D Sc m ν i (N1 i) (hN1 i) w n
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (n : ℕ) :=
  probeMatrixCharts_capDotRow D Sc m ν i (N1 i) (hN1 i) w n

/-- The first fields keep the actual canonical source/target parity maps. -/
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeMatrixCharts_unitEntry_none D Sc m ν i (N1 i) (hN1 i) b w
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeMatrixCharts_capEntry_none D Sc m ν i (N1 i) (hN1 i) b w

/-- Every dotted field uses the same given maps and canonical slot chart. -/
example (i : Bool) (b : ℕ) (r : Fin b) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeMatrixCharts_unitEntry_some D Sc m ν i (N1 i) (hN1 i) b r w
example (i : Bool) (b : ℕ) (r : Fin b) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeMatrixCharts_capEntry_some D Sc m ν i (N1 i) (hN1 i) b r w

/-- The complete finite-field comparison has no compatibility assumption. -/
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (r : Option (Fin b)) :=
  probeMatrixCharts_unitEntry D Sc m ν i (N1 i) (hN1 i) b w r
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (r : Option (Fin b)) :=
  probeMatrixCharts_capEntry D Sc m ν i (N1 i) (hN1 i) b w r

private def M01 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 1)
private def N01 (i : Bool) := probeOldModule D m Sc [i] M01
private abbrev hN01 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc [i] M01
private abbrev w0 (i : Bool) : ELVOld.OldContentCategory D Sc cut [i] :=
  ELVOld.oldContentObject D Sc cut [i] ⟨[i],List.Perm.refl [i]⟩

/-- Vacuum includes both complete zero-size matrices and their mate fields. -/
example (i : Bool) :=
  probeMatrixCharts_unitEntry D Sc m [] i (N01 i) (hN01 i) 0 (w0 i) none
example (i : Bool) :=
  probeMatrixCharts_capEntry D Sc m [] i (N01 i) (hN01 i) 0 (w0 i) none

end ProbeMatrixEntryComparisonConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixEntryComparison
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
