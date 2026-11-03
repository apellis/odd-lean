import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingColourMatrix
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace ProbeMissingColourMatrixConsumer
private abbrev D := datum
private abbrev Sc := scalars
private def m : Bool → ℕ := fun i => if i then 4 else 3
private abbrev cut := probeCutoff D m
private abbrev a : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private abbrev γ (i : Bool) : List Bool := [!i]
private def M1 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 1)
private def N1 (i : Bool) := probeOldModule D m Sc (γ i) M1
private abbrev hN1 (i : Bool) := probeOldModule_evaluatesCoefficients D m Sc (γ i) M1
private def O1 (i : Bool) := probeOrdinaryModuleSuperfunctor D Sc m (γ i) (N1 i) (hN1 i)
private def M0 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private def N0 := probeOldModule D m Sc [] M0
private abbrev hN0 := probeOldModule_evaluatesCoefficients D m Sc [] M0

private theorem absent (i : Bool) : i ∉ γ i := by cases i <;> decide
private theorem absent0 (i : Bool) : i ∉ ([] : List Bool) := by simp
/-- Both parities at nonempty output lacking the moving colour, with the
coefficient-evaluating module and absent-colour proof explicitly supplied. -/
example (i : Bool) (w : OldContentCategory D Sc cut (γ i)) :=
  probeMissingColourUnitMatrixIso D Sc m (γ i) (N1 i) (hN1 i) i (absent i) w
example (i : Bool) (w : OldContentCategory D Sc cut (γ i)) :=
  probeMissingColourUnitMatrixIso_hom D Sc m (γ i) (N1 i) (hN1 i) i (absent i) w
example (i : Bool) (w : OldContentCategory D Sc cut (γ i)) :=
  probeMissingColourUnitMatrixIso_hom_mem D Sc m (γ i) (N1 i) (hN1 i) i (absent i) w
example (i : Bool) (w : OldContentCategory D Sc cut (γ i)) :=
  probeMissingColourUnitMatrixIso_inv_mem D Sc m (γ i) (N1 i) (hN1 i) i (absent i) w
example (i : Bool) (w : OldContentCategory D Sc cut (γ i)) :=
  (probeMissingColourUnitMatrixIso D Sc m (γ i) (N1 i) (hN1 i) i (absent i) w).hom_inv_id
example (i : Bool) (w : OldContentCategory D Sc cut (γ i)) :=
  (probeMissingColourUnitMatrixIso D Sc m (γ i) (N1 i) (hN1 i) i (absent i) w).inv_hom_id

/-- Genuine empty output has the same identified prescribed unit-matrix
inverse, rather than merely the output[i] vacuum predecessor case. -/
example (i : Bool) (w : OldContentCategory D Sc cut []) :=
  probeMissingColourUnitMatrixIso D Sc m [] N0 hN0 i (absent0 i) w
example (i : Bool) (w : OldContentCategory D Sc cut []) :=
  probeMissingColourUnitMatrixIso_hom D Sc m [] N0 hN0 i (absent0 i) w
example (i : Bool) (w : OldContentCategory D Sc cut []) :=
  probeMissingColourUnitMatrixIso_hom_mem D Sc m [] N0 hN0 i (absent0 i) w
example (i : Bool) (w : OldContentCategory D Sc cut []) :=
  probeMissingColourUnitMatrixIso_inv_mem D Sc m [] N0 hN0 i (absent0 i) w
example (i : Bool) (w : OldContentCategory D Sc cut []) :=
  (probeMissingColourUnitMatrixIso D Sc m [] N0 hN0 i (absent0 i) w).hom_inv_id
example (i : Bool) (w : OldContentCategory D Sc cut []) :=
  (probeMissingColourUnitMatrixIso D Sc m [] N0 hN0 i (absent0 i) w).inv_hom_id

private def mZero : Bool → ℕ := fun _ => 0
private abbrev aZero : Bool → Polynomial ℚ := probePolynomial (probeDotExponent D) mZero
private def MZero := SuperBimodule.regular
  (heightParity D Sc aZero (probePolynomial_parity D mZero) 0)
private def NZero := probeOldModule D mZero Sc [] MZero
private abbrev hNZero := probeOldModule_evaluatesCoefficients D mZero Sc [] MZero
/-- At zero cutoff and genuine empty output the given matrix has zero
remaining columns; its target is consequently zero as well. -/
example (i : Bool) : CyclotomicCrossingTensor.contentUnitCount D (probeCutoff D mZero) i
    (0 : Multiset Bool) = 0 := by cases i <;> decide
example (i : Bool) (w : OldContentCategory D Sc (probeCutoff D mZero) []) :=
  probeMissingColourUnitMatrixIso_hom D Sc mZero [] NZero hNZero i (absent0 i) w
example (i : Bool) (w : OldContentCategory D Sc (probeCutoff D mZero) []) :=
  (probeMissingColourUnitMatrixIso D Sc mZero [] NZero hNZero i (absent0 i) w).hom_inv_id
example (i : Bool) (w : OldContentCategory D Sc (probeCutoff D mZero) []) :=
  (probeMissingColourUnitMatrixIso D Sc mZero [] NZero hNZero i (absent0 i) w).inv_hom_id

end ProbeMissingColourMatrixConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingColourMatrix
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
