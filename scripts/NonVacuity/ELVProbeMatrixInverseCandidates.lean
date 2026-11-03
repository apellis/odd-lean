import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixInverseCandidates
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace ProbeMatrixInverseCandidatesConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private abbrev ν : List Bool := [false,true]
private def M3 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 3)
private def N3 (i : Bool) := probeOldModule D m Sc (i :: ν) M3
private abbrev hN3 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc (i :: ν) M3
private abbrev w3 (i : Bool) : OldContentCategory D Sc cut (i :: ν) :=
  oldContentObject D Sc cut (i :: ν) ⟨i :: ν,List.Perm.refl _⟩
private theorem positive (i : Bool) :
    0 ≤ contentCrossingHeight D cut i ((w3 i).obj.word : Multiset Bool) := by
  cases i <;> decide

/-- Actual positive-height given old inverse on the selected full-content
extension, transported through both genuine chart families. -/
example (i : Bool) := probeTransportedUnitMatrixIso D Sc m ν i (N3 i) (hN3 i) (w3 i) (positive i)
example (i : Bool) :=
  (probeTransportedUnitMatrixIso D Sc m ν i (N3 i) (hN3 i) (w3 i) (positive i)).hom_inv_id
example (i : Bool) :=
  (probeTransportedUnitMatrixIso D Sc m ν i (N3 i) (hN3 i) (w3 i) (positive i)).inv_hom_id

private def one : Bool → ℕ := fun _ => 1
private abbrev cutOne := probeCutoff D one
private abbrev aOne : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) one
private def M1 := SuperBimodule.regular (heightParity D Sc aOne (probePolynomial_parity D one) 1)
private def N1 (i : Bool) := probeOldModule D one Sc [i] M1
private abbrev hN1 (i : Bool) := probeOldModule_evaluatesCoefficients D one Sc [i] M1
private abbrev w1 (i : Bool) : OldContentCategory D Sc cutOne [i] :=
  oldContentObject D Sc cutOne [i] ⟨[i],List.Perm.refl _⟩
private theorem negative (i : Bool) :
    contentCrossingHeight D cutOne i ((w1 i).obj.word : Multiset Bool) ≤ 0 := by
  cases i <;> decide

/-- Empty predecessor: the negative-height given inverse and both inverse laws.
The output is [i]; this does not stand for the separate empty-output branch. -/
example (i : Bool) := probeTransportedCapMatrixIso D Sc one [] i (N1 i) (hN1 i) (w1 i) (negative i)
example (i : Bool) :=
  (probeTransportedCapMatrixIso D Sc one [] i (N1 i) (hN1 i) (w1 i) (negative i)).hom_inv_id
example (i : Bool) :=
  (probeTransportedCapMatrixIso D Sc one [] i (N1 i) (hN1 i) (w1 i) (negative i)).inv_hom_id

private def M2 := SuperBimodule.regular (heightParity D Sc aOne (probePolynomial_parity D one) 2)
private def N2 (i : Bool) := probeOldModule D one Sc [i,i] M2
private abbrev hN2 (i : Bool) := probeOldModule_evaluatesCoefficients D one Sc [i,i] M2
private abbrev w2 (i : Bool) : OldContentCategory D Sc cutOne [i,i] :=
  oldContentObject D Sc cutOne [i,i] ⟨[i,i],List.Perm.refl _⟩
private theorem negativeTwo (i : Bool) :
    contentCrossingHeight D cutOne i ((w2 i).obj.word : Multiset Bool) ≤ 0 := by
  cases i <;> decide

/-- Both moving colours with nonzero prescribed negative-height counts. -/
example (i : Bool) := probeTransportedCapMatrixIso D Sc one [i] i (N2 i) (hN2 i) (w2 i) (negativeTwo i)
example (i : Bool) :=
  (probeTransportedCapMatrixIso D Sc one [i] i (N2 i) (hN2 i) (w2 i) (negativeTwo i)).inv_hom_id

/-- Positive height with empty predecessor keeps the same concrete charts. -/
private def MP1 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 1)
private def NP1 (i : Bool) := probeOldModule D m Sc [i] MP1
private abbrev hNP1 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc [i] MP1
private abbrev wp1 (i : Bool) : OldContentCategory D Sc cut [i] :=
  oldContentObject D Sc cut [i] ⟨[i],List.Perm.refl _⟩
private theorem positiveOne (i : Bool) :
    0 ≤ contentCrossingHeight D cut i ((wp1 i).obj.word : Multiset Bool) := by
  cases i <;> decide
example (i : Bool) := probeTransportedUnitMatrixIso D Sc m [] i (NP1 i) (hNP1 i) (wp1 i) (positiveOne i)

end ProbeMatrixInverseCandidatesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixInverseCandidates
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
