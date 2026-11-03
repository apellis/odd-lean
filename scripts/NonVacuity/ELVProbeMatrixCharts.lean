import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace ProbeMatrixChartsConsumer
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


/-- The selected original append chart is the previously computed map. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeAppendLinearEquiv_hom D Sc m ν N hN i w

example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeAppendLinearEquiv_mem D Sc m ν N hN i w

/-- The E/F source uses the actual restriction equality, and the F/E target
uses the original selected next-append isomorphism. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeMatrixSourceLinearEquiv_hom D Sc m ν i (N1 i) (hN1 i) w
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeMatrixTargetLinearEquiv_hom D Sc m ν i (N1 i) (hN1 i) w

/-- The actual E/F and F/E charts supply their two-sided inverse laws. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  (probeMatrixSourceLinearEquiv D Sc m ν i (N1 i) (hN1 i) w).symm_apply_apply

example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  (probeMatrixTargetLinearEquiv D Sc m ν i (N1 i) (hN1 i) w).apply_symm_apply

/-- Actual old/ordinary induced-module values use the shared canonical
shifted point chart, with both parities checked on the selected map. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2) :=
  shiftedModuleValueLinearEquiv_hom_mem
    (induced (J ν i) N) ((induction (T ν i)).obj O) w ((Q (i :: ν)).obj w)
    (probeAppendLinearEquiv D Sc m ν N hN i w) q
    (probeAppendLinearEquiv_mem D Sc m ν N hN i w)

example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (q : ZMod 2) :=
  shiftedModuleValueLinearEquiv_inv_mem
    (induced (J ν i) N) ((induction (T ν i)).obj O) w ((Q (i :: ν)).obj w)
    (probeAppendLinearEquiv D Sc m ν N hN i w) q
    (probeAppendLinearEquiv_mem D Sc m ν N hN i w)

private def M0 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private def N0 := probeOldModule D m Sc [] M0
private abbrev hN0 := probeOldModule_evaluatesCoefficients D m Sc [] M0

/-- Vacuum still has the genuine selected append equivalence. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut [i]) :=
  probeAppendLinearEquiv_hom D Sc m [] N0 hN0 i w

end ProbeMatrixChartsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixCharts
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
