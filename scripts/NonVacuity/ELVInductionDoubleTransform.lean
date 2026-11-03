import OddMath.QuiverHecke.CyclotomicAction.ELVInductionDoubleTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendTensors
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld.BalancedInduction
open OddMath.QuiverHecke.ELVOld.WeightedAppendFixture
open OddMath.QuiverHecke.CyclotomicAction OddMath.SKM.SYM
namespace InductionDoubleTransformConsumer
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

/-- The canonical flattening-conjugated old crossing on mixed content. -/
example (i : Bool) (s : ELVOld.OldContentCategory D Sc cut ν)
    (v : ELVOld.OldContentCategory D Sc cut (i :: ν))
    (w : ELVOld.OldContentCategory D Sc cut (i :: i :: ν))
    (f : (J ν i).obj s ⟶ v) (g : (J (i :: ν) i).obj v ⟶ w)
    (b : N.obj s) :=
  doubleTransformLinear_tensor (J ν i) (J (i :: ν) i)
    (probeOldContentEqualCross_supernatural D Sc m ν i) N s v w f g b

/-- The raw operator is the total component of the prescribed module conjugate. -/
example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: i :: ν))
    (b : Obj (J (i :: ν) i) (induced (J ν i) N).toFunctor w) :=
  doubleTransformLinear_eq_total (J ν i) (J (i :: ν) i)
    (probeOldContentEqualCross_supernatural D Sc m ν i) N w b

example (i : Bool) (w : ELVOld.OldContentCategory D Sc cut (i :: i :: ν)) :
    (LinearMap.id : Obj (J (i :: ν) i) (induced (J ν i) N).toFunctor w →ₗ[ℚ]
      Obj (J (i :: ν) i) (induced (J ν i) N).toFunctor w) = LinearMap.id :=
  doubleHom_ext (J ν i) (J (i :: ν) i) N (fun _ _ _ _ _ => rfl)

private def M0 := SuperBimodule.regular (heightParity D Sc a (probePolynomial_parity D m) 0)
private def N0 := probeOldModule D m Sc [] M0
private abbrev hN0 := probeOldModule_evaluatesCoefficients D m Sc [] M0
private def O0 := probeOrdinaryModuleSuperfunctor D Sc m [] N0 hN0
private abbrev s0 : ELVOld.OldContentCategory D Sc cut [] :=
  ELVOld.oldContentObject D Sc cut [] ⟨[],List.Perm.refl []⟩

/-- Vacuum includes the repeated odd crossing on the two unit tensors. -/
example (i : Bool) (b : N0.obj s0) :=
  doubleTransformLinear_tensor (J [] i) (J [i] i)
    (probeOldContentEqualCross_supernatural D Sc m [] i) N0
    s0 ((J [] i).obj s0) ((J [i] i).obj ((J [] i).obj s0)) (𝟙 _) (𝟙 _) b

end InductionDoubleTransformConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionDoubleTransform
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."
