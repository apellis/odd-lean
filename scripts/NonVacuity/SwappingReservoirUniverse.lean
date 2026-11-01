import OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingReservoir
import OddMath.QuiverHecke.SwappedAssembly.Sigma.AugmentedMatrix
import OddMath.QuiverHecke.SwappedAssembly.Sigma.MixedEntry
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirProbeEntry
import StringDiagrams.Super.PiTwo
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath.SKM
open OddMath.QuiverHecke.SwappedAssembly
universe u
local instance {k : Type u} [CommRing k]
    (A B : PiSCat.{u, u, u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : Datum I X} {Sc : Scalars D k}
  (P : ProbeReservoir k (PiSCat.{u, u, u + 1} k) D Sc)
example (c : P.CrossCoeff) (hc : c.IsInverse)
    (hD : P.CrossDenominatorUnits) (hS : P.CrossTransposeNormUnits)
    (hcentral : P.CentralInvertible c) : P.AugmentedInvertible c :=
  ProbeReservoir.augmentedInvertible_of_central_of_units c hc hD hS hcentral

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : Array Name := #[`OddMath.QuiverHecke.SwappedAssembly.Supernatural.Leftward,
    `OddMath.QuiverHecke.SwappedAssembly.LeftwardInverse,
    `OddMath.QuiverHecke.SwappedAssembly.Sigma.SameColourBlocks,
    `OddMath.QuiverHecke.SwappedAssembly.Sigma.Entry,
    `OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingEntries,
    `OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingMate,
    `OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingReservoir,
    `OddMath.QuiverHecke.SwappedAssembly.Sigma.AugmentedMatrix,
    `OddMath.QuiverHecke.SwappedAssembly.Sigma.MixedEntry,
    `OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirProbeEntry]
  let mut count := 0
  for owner in owners do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Module was not imported: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    unless names.size > 0 do throwError "Empty owned declaration inventory: {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    count := count + names.size
  logInfo m!"Audited ALL {count} declarations across {owners.size} universe-corrected modules"
