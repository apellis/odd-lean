import OddMath.QuiverHecke.PairingExtensionObservation
import OddMath.QuiverHecke.SwappedVacuumParameters
import OddMath.QuiverHecke.SwappedAssembly.SupportedAction
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorFamilies
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumUnit
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.CyclotomicAction
open SwappedVacuumParameters
namespace NonVacuity.PairingExtensionObservation
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


private def cs : SKM.CScalars Sc where
  c ν _ := if ν.2 = 0 then 1 else -1
  shift ν i j := by
    change (if ν.2 + 0 = 0 then (1 : ℚˣ) else -1) = 1 * (if ν.2 = 0 then 1 else -1)
    simp
private def idx : SKM.SYM.CoefficientIndex D := (Finsupp.single (false,0) 1, {⟨true,rfl⟩})
private def a : SKM.SYM D ℚ := SKM.SYM.coefficientBasis D ℚ idx
example : a ≠ 0 := (SKM.SYM.coefficientBasis D ℚ).ne_zero _
private theorem aw : SKM.SYM.coefficientWeight D idx = 2 := by
  norm_num [SKM.SYM.coefficientWeight, SKM.SYM.elementaryWeight, idx, D]
private theorem ha : a ∈ SKM.SYM.CoefficientAtMost D ℚ 2 :=
  Submodule.subset_span ⟨idx, by change SKM.SYM.coefficientWeight D idx ≤ 2; rw [aw], rfl⟩
private theorem hl : a ∈ SKM.SYM.CoefficientAtLeast D ℚ 2 :=
  Submodule.subset_span ⟨idx, by change 2 ≤ SKM.SYM.coefficientWeight D idx; rw [aw], rfl⟩

example : SKM.PairingExtension.coefficientEquiv D a ∈ SKM.SYM.CoefficientAtMost De ℚ 2 :=
  QuiverHecke.PairingExtension.coefficientEquiv_mem_atMost D ha
example : SKM.PairingExtension.coefficientEquiv D a ∈ SKM.SYM.CoefficientAtLeast De ℚ 2 :=
  QuiverHecke.PairingExtension.coefficientEquiv_mem_atLeast D hl

example : (extendedAction.restrictPairingExtension D Sc μ).bubbles cs s a =
    extendedAction.bubbles (ReservoirWeights.pairingExtensionCScalars D cs) s
      (SKM.PairingExtension.coefficientEquiv D a) :=
  UpwardModuleAction.restrictPairingExtension_bubbles D Sc cs μ extendedAction s a

private def cross : ob D [false,true] ⟶ ob D [true,false] :=
  mkD D [([], Shape.cross false true, [])] (by exact ⟨rfl,rfl⟩)
example : (extendedAction.restrictPairingExtension D Sc μ).act [false,true] [true,false]
    ((alpha D Sc μ).map ((pres D Sc).diag cross)) =
    extendedAction.act [false,true] [true,false] ((alpha De Se (μ,0)).map
      ((QuiverHecke.PairingExtension.presentationFunctor D Sc).map ((pres D Sc).diag cross))) :=
  UpwardModuleAction.restrictPairingExtension_upAct D Sc μ extendedAction ((pres D Sc).diag cross)

example (i : Bool) : probeOldVacuumAppendVector De (parameterTwist De Se) m i ≠ 0 :=
  probeOldVacuumAppendVector_ne_zero De (parameterTwist De Se) m i (probeExponent_pos D μ s 2 i)
end NonVacuity.PairingExtensionObservation
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.PairingExtensionObservation
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations: standard axioms only"
