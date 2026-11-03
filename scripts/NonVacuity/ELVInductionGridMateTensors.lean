import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMateTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace InductionGridMateTensorsConsumer
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

/-- The old mate uses different append adjunctions at successive contents. -/
example (i : Bool) (s : ELVOld.OldContentCategory D Sc cut ν)
    (t : ELVOld.OldContentCategory D Sc cut (i :: ν))
    (g : (J ν i).obj s ⟶ t) (b : (N1 i).obj ((J ν i).obj s)) :=
  orderedGridMateLinear_tensor (J ν i) (J (i :: ν) i)
    (probeOldContentEqualCross_supernatural D Sc m ν i) (N1 i) s t g b

/-- The raw map is the given mate's total component on every coend vector. -/
example (i : Bool) (t : ELVOld.OldContentCategory D Sc cut (i :: ν))
    (b : Obj (J ν i) ((restriction (J ν i)).obj (N1 i)).toFunctor t) :=
  orderedGridMateLinear_apply (J ν i) (J (i :: ν) i)
    (probeOldContentEqualCross_supernatural D Sc m ν i) (N1 i) t b

/-- The ordinary mate has its literal unit, crossing and counit, for both parities. -/
example (i : Bool)
    (s : OrdinaryContentCategory D Sc a ν)
    (t : OrdinaryContentCategory D Sc a (i :: ν))
    (g : (T ν i).obj s ⟶ t) (b : (O1 i).obj ((T ν i).obj s)) :=
  orderedGridMateLinear_tensor (T ν i) (T (i :: ν) i)
    (probeOrdinaryEqualCross_supernatural D Sc m ν i) (O1 i) s t g b

private def M0 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private def N0 := probeOldModule D m Sc [] M0
private abbrev hN0 := probeOldModule_evaluatesCoefficients D m Sc [] M0
private def O0 := probeOrdinaryModuleSuperfunctor D Sc m [] N0 hN0
private abbrev s0 : ELVOld.OldContentCategory D Sc cut [] :=
  ELVOld.oldContentObject D Sc cut [] ⟨[],List.Perm.refl []⟩

private def M01 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 1)
private def N01 (i : Bool) := probeOldModule D m Sc [i] M01

/-- Vacuum tests the first nontrivial mate and the repeated odd crossing. -/
example (i : Bool) (b : (N01 i).obj ((J [] i).obj s0)) :=
  orderedGridMateLinear_tensor (J [] i) (J [i] i)
    (probeOldContentEqualCross_supernatural D Sc m [] i) (N01 i)
    s0 ((J [] i).obj s0) (𝟙 _) b

end InductionGridMateTensorsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMateTensors
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
