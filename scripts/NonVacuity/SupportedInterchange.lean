import NonVacuity.PointwiseLeftwardFixture
import OddMath.QuiverHecke.SwappedAssembly.SupportedInterchange
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorFamilies
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.SupportedInterchange
open PointwiseLeftwardFixture
local instance homPi (A C : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C

private def selectedFamily (s : Sector Bool) : SupportedSectors.H D Sc m cutoff N Λ Λ s := by
  classical
  exact if h : s = t then h.symm ▸ supportedPath
    else SupportedSectors.supportedZero D Sc m cutoff N Λ Λ s
private def rawFamily (s : Sector Bool) : P.H s := (selectedFamily s).obj
private theorem selectedFamily_nonzero : ¬Limits.IsZero (rawFamily t) := by
  simpa [rawFamily,selectedFamily] using supportedPath_nonzero
private theorem hC : chosen.IsSupernatural :=
  elvProbeCrossCoeff_isSupernatural D originalSc m cutoff N Λ Λ
    probePairing reservoirPairing sy homogeneous

private theorem upward_naturality :
    ProbeReservoir.GeneratorsSupernaturalOn
      (SupportedSectors.retainedInput D originalSc m cutoff N Λ Λ probePairing reservoirPairing)
      (P.upwardGens chosen) := by
  intro g a b p q
  let J := SupportedSectors.inclusion D Sc m cutoff N Λ Λ b
  let : J.Additive := SupportedSectors.inclusion_additive D Sc m cutoff N Λ Λ b
  let : J.Linear ℚ := SupportedSectors.inclusion_linear D Sc m cutoff N Λ Λ b
  let : IsSuperfunctor ℚ J := SupportedSectors.inclusion_super D Sc m cutoff N Λ Λ b
  exact (ProbeReservoir.upwardGens_supernatural chosen hC g p q).whiskerLeft J

-- The theorem is applied to a retained family with a proved nonzero sector.
example : InterchangeLaw (P.layerRep rawFamily rawFamily (P.upwardGens chosen)) :=
  ProbeReservoir.interchangeLaw_on
    (SupportedSectors.retainedInput D originalSc m cutoff N Λ Λ probePairing reservoirPairing)
    (SupportedSectors.retainedInput_path D originalSc m cutoff N Λ Λ probePairing reservoirPairing)
    rawFamily rawFamily (fun s => (selectedFamily s).property) upward_naturality
example : ¬Limits.IsZero (rawFamily t) := selectedFamily_nonzero
end NonVacuity.SupportedInterchange

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.SupportedInterchange
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"Auditing {names.size} owned declarations in {owner}"
