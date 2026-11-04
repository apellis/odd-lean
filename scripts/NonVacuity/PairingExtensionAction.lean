import OddMath.QuiverHecke.PairingExtensionAction
import OddMath.QuiverHecke.SwappedVacuumParameters
import OddMath.QuiverHecke.SwappedAssembly.SupportedAction
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorFamilies
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.CyclotomicAction
open SwappedVacuumParameters
namespace NonVacuity.PairingExtensionAction
/-- Connected mixed colours and an independent common coroot-kernel coordinate. -/
private def D : SKM.Datum Bool ((Bool → ℤ) × ℤ) where
  cd :=
    { root := fun j => (fun i => if i = j then 2 else -2, 0)
      coroot := fun i => (LinearMap.proj i).comp (LinearMap.fst ℤ (Bool → ℤ) ℤ)
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun i => if i then 1 else 0
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else -2)
    split_ifs <;> norm_num

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => (by norm_num : (2 : ℚ) ≠ 0).isUnit

private def μ : (Bool → ℤ) × ℤ := (fun i => if i then -5 else 3, 7)
private def s : List Bool := [false, true, false]


private abbrev De := ReservoirWeights.pairingExtension D
private abbrev Se := ReservoirWeights.pairingExtensionScalars D Sc
private def sy : SKM.Symmetrizer D where
  d := fun _ => 1
  pos := fun _ => by norm_num
  symm := by
    intro i j
    simp [D, SKM.Datum.d, SKM.Datum.h, SKM.Datum.α, eq_comm]
private theorem hc : Sc.Homogeneous := by
  intro _ _ _ _ _ _ _ _ h
  exact (h rfl).elim
private abbrev sye := ReservoirWeights.pairingExtensionSymmetrizer D sy
private theorem hce : Se.Homogeneous := ReservoirWeights.pairingExtensionScalars_homogeneous D Sc hc
private abbrev m := probeExponent D μ s 2
private abbrev cutoff := reservoirLevel D μ s 2
private abbrev lp := probeWeight D μ s 2
private abbrev lr := reservoirWeight D μ s 2
private theorem hp (i : Bool) : (probeCutoff De m i : ℤ) = De.h i lp := probe_pairing D μ s 2 i
private theorem hr (i : Bool) : (cutoff i : ℤ) = De.h i lr := reservoir_pairing D μ s 2 i
private abbrev powers := coefficientPower s 2
private abbrev bound := PowerWordContent.powerBound De cutoff powers
private def Gs := SwappedAssembly.SupportedSectors.tensorSourceFamily De Se m cutoff lp lr powers s
private def Ys := SwappedAssembly.SupportedSectors.tensorTargetFamily De Se m cutoff lp lr powers
private def extendedAction : UpwardModuleAction De Se (μ,0) :=
  SwappedAssembly.SupportedSectors.pointwiseUpwardModuleAction De Se m cutoff bound lp lr hp hr
    sye hce Gs Ys (μ,0)

/-- The original-datum action is constructed from the exact extended supported model. -/
example : UpwardModuleAction D Sc μ := extendedAction.restrictPairingExtension D Sc μ

example : (extendedAction.restrictPairingExtension D Sc μ).V s = extendedAction.V s := rfl

/-- Both actual probe summands have a nonzero vector; no nonzero-action premise is assumed. -/
example (i : Bool) : probeOldVacuumAppendVector De (parameterTwist De Se) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero De (parameterTwist De Se) m i (probeExponent_pos D μ s 2 i)

/-- The original coroot-kernel coordinate survives in the target region. -/
example : ((SKM.PairingExtension.inclusion D).region μ).1.2 = 7 := rfl

private def oddDot : SKM.ob D μ [SKM.up true] ⟶ SKM.ob D μ [SKM.up true] :=
  SKM.mkD D μ [([], SKM.Shape.dot true, [])] (by exact ⟨rfl, rfl⟩)

example : SKM.PairingExtension.homMap D Sc μ [SKM.up true] [SKM.up true]
    ((SKM.pres D Sc).diag oddDot) =
      (SKM.pres De Se).diag (SKM.PairingExtension.diagram D oddDot) :=
  SKM.PairingExtension.homMap_diag D Sc oddDot

/-- The free diagram comparison is nonzero at the retained region. -/
example : SKM.PairingExtension.linear (k := ℚ) D μ [SKM.up true] [SKM.up true]
    (LinDiagram.of oddDot) ≠ 0 := by
  rw [SKM.PairingExtension.linear_of]
  change Finsupp.single (SKM.PairingExtension.diagram D oddDot) (1 : ℚ) ≠ 0
  simp

/-- Both finite inverse windows are transported without an assumed relation identity. -/
example : (SKM.pres De Se).lin
    (SKM.PairingExtension.linear D μ [SKM.dn false, SKM.up false] []
      (SKM.relation D Sc (.invP₃ false μ 1 (by decide)))) = 0 :=
  SKM.PairingExtension.linear_relation_zero D Sc (.invP₃ false μ 1 (by decide))

example : (SKM.pres De Se).lin
    (SKM.PairingExtension.linear D μ [] [SKM.up true, SKM.dn true]
      (SKM.relation D Sc (.invM₃ true μ 1 (by decide)))) = 0 :=
  SKM.PairingExtension.linear_relation_zero D Sc (.invM₃ true μ 1 (by decide))

end NonVacuity.PairingExtensionAction

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.SKM.PairingExtensionDiagrams,
      `OddMath.SKM.PairingExtensionPresentation, `OddMath.QuiverHecke.PairingExtensionAction] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned declarations"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}: standard axioms only"
