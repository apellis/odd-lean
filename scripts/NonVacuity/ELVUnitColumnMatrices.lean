import OddMath.QuiverHecke.CyclotomicAction.ELVProbeUpperCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitColumnMatrices
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace UnitColumnMatricesConsumer
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

private abbrev K (γ : List Bool) (i : Bool) := oldContentAppend D Sc cut γ i
private abbrev S (γ : List Bool) (i : Bool) := probeOrdinaryAppend D Sc m γ i
private abbrev U (γ : List Bool) := probeOldOrdinaryFunctor D Sc m γ
private abbrev dK (γ : List Bool) (i : Bool) := probeOldContentAppendDot_supernatural D Sc m γ i
private abbrev dS (γ : List Bool) (i : Bool) := probeOrdinaryAppendDot_supernatural D Sc m γ i

/-- The finite comparison has its ALL-powers premise proved by the selected
scalar following/value chart theorem, for both moving parities. -/
example (i : Bool) (w : OldContentCategory D Sc cut (γ i)) (b : ℕ) :=
  unitColumnMatrix_square (K (γ i) i) (S (γ i) i) (dK (γ i) i) (dS (γ i) i)
    (N1 i) (O1 i) w ((U (γ i)).obj w)
    (probeOutputValueLinearEquiv D Sc m (γ i) (N1 i) (hN1 i) w)
    (probeOutputFELinearEquiv D Sc m (γ i) (N1 i) (hN1 i) i w).toLinearMap
    (probeOutputFELinearEquiv_unitDot D Sc m (γ i) (N1 i) (hN1 i) i w) b
example (i : Bool) (w : OldContentCategory D Sc cut (γ i)) (b : ℕ) :=
  unitColumnMatrix_mem (S (γ i) i) (dS (γ i) i) (O1 i) b ((U (γ i)).obj w)
example (i : Bool) (w : OldContentCategory D Sc cut (γ i)) (b : ℕ) :=
  (unitColumnFamilyEquiv (N1 i) (O1 i) w ((U (γ i)).obj w)
    (probeOutputValueLinearEquiv D Sc m (γ i) (N1 i) (hN1 i) w) (D.parity i) b).apply_symm_apply
private def O0 := probeOrdinaryModuleSuperfunctor D Sc m [] N0 hN0
/-- Genuine empty output, all finite counts (including zero and one). -/
example (i : Bool) (w : OldContentCategory D Sc cut []) (b : ℕ) :=
  unitColumnMatrix_square (K [] i) (S [] i) (dK [] i) (dS [] i) N0 O0 w ((U []).obj w)
    (probeOutputValueLinearEquiv D Sc m [] N0 hN0 w)
    (probeOutputFELinearEquiv D Sc m [] N0 hN0 i w).toLinearMap
    (probeOutputFELinearEquiv_unitDot D Sc m [] N0 hN0 i w) b
example (i : Bool) (w : OldContentCategory D Sc cut []) :=
  unitColumnMatrix_mem (S [] i) (dS [] i) O0 0 ((U []).obj w)
example (i : Bool) (w : OldContentCategory D Sc cut []) :=
  unitColumnMatrix_mem (S [] i) (dS [] i) O0 1 ((U []).obj w)

end UnitColumnMatricesConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVUnitColumnMatrices
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
