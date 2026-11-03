import OddMath.QuiverHecke.CyclotomicAction.ELVProbeUpperCharts
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace ProbeUpperChartsConsumer
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

/-- Both moving parities at output containing only the other colour. -/
example (i : Bool) (w : OldContentCategory D Sc cut (γ i)) :=
  probeOutputValueLinearEquiv D Sc m (γ i) (N1 i) (hN1 i) w
example (i : Bool) (w : OldContentCategory D Sc cut (γ i)) (b : (N1 i).obj w) :=
  probeOutputValueLinearEquiv_apply D Sc m (γ i) (N1 i) (hN1 i) w b
example (i : Bool) (w : OldContentCategory D Sc cut (γ i))
    (b : (O1 i).obj ((probeOldOrdinaryFunctor D Sc m (γ i)).obj w)) :=
  probeOutputValueLinearEquiv_symm_apply D Sc m (γ i) (N1 i) (hN1 i) w b
example (i : Bool) (w : OldContentCategory D Sc cut (γ i)) :=
  probeOutputFELinearEquiv_hom D Sc m (γ i) (N1 i) (hN1 i) i w
example (i : Bool) (w : OldContentCategory D Sc cut (γ i)) (n : ℕ) :=
  probeOutputFELinearEquiv_unitDot D Sc m (γ i) (N1 i) (hN1 i) i w n
example (i : Bool) (w : OldContentCategory D Sc cut (γ i)) :=
  (probeOutputFELinearEquiv D Sc m (γ i) (N1 i) (hN1 i) i w).apply_symm_apply

/-- Genuine empty output also retains both invertible charts and all columns. -/
example (w : OldContentCategory D Sc cut []) := probeOutputValueLinearEquiv D Sc m [] N0 hN0 w
example (i : Bool) (w : OldContentCategory D Sc cut []) :=
  probeOutputFELinearEquiv_hom D Sc m [] N0 hN0 i w
example (i : Bool) (w : OldContentCategory D Sc cut []) (n : ℕ) :=
  probeOutputFELinearEquiv_unitDot D Sc m [] N0 hN0 i w n
example (i : Bool) (w : OldContentCategory D Sc cut []) :=
  (probeOutputFELinearEquiv D Sc m [] N0 hN0 i w).symm_apply_apply
end ProbeUpperChartsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVProbeUpperCharts
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
