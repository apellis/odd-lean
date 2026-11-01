import OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingReservoir
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath.SKM
open OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.SwappingReservoir
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k} (P : ProbeReservoir k B D Sc)

/-- The augmented-block interface accepts the literal norm inputs, with
no whole-dot nilpotence hypothesis. Concrete norm producers are tested in TransposeNorms. -/
example (c : P.CrossCoeff) (hc : c.IsInverse)
    (hD : P.CrossDenominatorUnits) (hS : P.CrossTransposeNormUnits)
    (hcentral : P.CentralInvertible c) : P.AugmentedInvertible c :=
  ProbeReservoir.augmentedInvertible_of_central_of_units c hc hD hS hcentral

/-- Existing callers retain the former sufficient whole-dot interface. -/
example (c : P.CrossCoeff) (hc : c.IsInverse)
    (hT : ∀ (i : I) {x y : X} (h : x + D.α i = y),
      IsUnit (show End (P.T.E i h) from P.T.dot i h))
    (hW : ∀ (i : I) {x y : X} (h : x + D.α i = y),
      IsNilpotent (show End (P.W.E i h) from P.W.dot i h))
    (hcentral : P.CentralInvertible c) : P.AugmentedInvertible c :=
  ProbeReservoir.augmentedInvertible_of_central c hc hT hW hcentral

end NonVacuity.SwappingReservoir

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingReservoir
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
