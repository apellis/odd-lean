import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixFamilyCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace ProbeMatrixFamilyChartsConsumer
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


/-- The selected value, E/F and F/E charts are even on actual module values. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeMatrixValueLinearEquiv_mem D Sc m ν i (N1 i) (hN1 i) w
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeMatrixSourceLinearEquiv_mem D Sc m ν i (N1 i) (hN1 i) w
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeMatrixTargetLinearEquiv_mem D Sc m ν i (N1 i) (hN1 i) w

example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (b : (N1 i).obj w) :=
  probeMatrixValueLinearEquiv_apply D Sc m ν i (N1 i) (hN1 i) w b
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: ν))
    (b : (O1 i).obj ((Q (i :: ν)).obj w)) :=
  probeMatrixValueLinearEquiv_symm_apply D Sc m ν i (N1 i) (hN1 i) w b

/-- Every literal Option/Fin slot, for both moving parities and all sizes. -/
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (r : Option (Fin b)) :=
  probeUnitMatrixSlotLinearEquiv_mem D Sc m ν i (N1 i) (hN1 i) b w r
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) (r : Option (Fin b)) :=
  probeCapMatrixSlotLinearEquiv_mem D Sc m ν i (N1 i) (hN1 i) b w r

/-- Both whole selected family charts and their genuine inverses are even. -/
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeUnitMatrixFamilyLinearEquiv_mem D Sc m ν i (N1 i) (hN1 i) b w
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeCapMatrixFamilyLinearEquiv_mem D Sc m ν i (N1 i) (hN1 i) b w
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeUnitMatrixFamilyLinearEquiv_inv_mem D Sc m ν i (N1 i) (hN1 i) b w
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeCapMatrixFamilyLinearEquiv_inv_mem D Sc m ν i (N1 i) (hN1 i) b w

/-- The full charts preserve their specified slot coordinate maps on every vector. -/
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeUnitMatrixFamilyLinearEquiv_apply D Sc m ν i (N1 i) (hN1 i) b w
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  probeCapMatrixFamilyLinearEquiv_apply D Sc m ν i (N1 i) (hN1 i) b w

example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  (probeUnitMatrixFamilyLinearEquiv D Sc m ν i (N1 i) (hN1 i) b w).symm_apply_apply
example (i : Bool) (b : ℕ) (w : ELVOld.OldContentCategory D Sc cut (i :: ν)) :=
  (probeCapMatrixFamilyLinearEquiv D Sc m ν i (N1 i) (hN1 i) b w).apply_symm_apply

private def M01 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 1)
private def N01 (i : Bool) := probeOldModule D m Sc [i] M01
private abbrev hN01 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc [i] M01
private abbrev w0 (i : Bool) : ELVOld.OldContentCategory D Sc cut [i] :=
  ELVOld.oldContentObject D Sc cut [i] ⟨[i],List.Perm.refl [i]⟩

/-- Vacuum includes the first slot when there are zero dotted summands. -/
example (i : Bool) :=
  probeUnitMatrixFamilyLinearEquiv_mem D Sc m [] i (N01 i) (hN01 i) 0 (w0 i)
example (i : Bool) :=
  probeCapMatrixFamilyLinearEquiv_mem D Sc m [] i (N01 i) (hN01 i) 0 (w0 i)

end ProbeMatrixFamilyChartsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixFamilyCharts
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
