import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.InterchangePostPairTransport
import Lean.Util.CollectAxioms

/-! Arbitrary occupied-content validation of the transport prerequisite only.
This does not assert the forward braid sector or an independent representation. -/
noncomputable section
namespace NonVacuity.MixedDistinctReservoirTransport
open CategoryTheory StringDiagrams OddMath.SKM
open OddMath.QuiverHecke.SwappedAssembly
open OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
variable {I X : Type} [AddCommGroup X] {k : Type} [CommRing k]
  {B : Type} [BicategoryStruct.{0, 0} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k} (P : ProbeReservoir k B D Sc)
example (i r q : I) (β γ : I →₀ ℕ)
    (Z : P.H (nextSector (true, i) true
      (nextSector (true, r) false (nextSector (true, q) false
        (β, γ + Finsupp.single r 1 + Finsupp.single q 1))))) :
    let s : Sector I := (β, γ + Finsupp.single r 1 + Finsupp.single q 1)
    let h : nextSector (true, q) false (nextSector (true, r) false s) =
        nextSector (true, r) false (nextSector (true, q) false s) := by
      simp only [nextSector, tsub_right_comm]
    (P.step (true, i) true (nextSector (true, q) false
      (nextSector (true, r) false s)) trivial).obj
        ((congrArg (nextSector (true, i) true) h) ▸ Z) =
      h ▸ (P.step (true, i) true (nextSector (true, r) false
        (nextSector (true, q) false s)) trivial).obj Z := by
  dsimp only
  exact P.probe_obj_sector_transport i (by simp only [nextSector, tsub_right_comm]) Z
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.resCore_mixedInterchange_transport
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.probe_obj_sector_transport
end NonVacuity.MixedDistinctReservoirTransport

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mod := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.InterchangePostPairTransport
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == mod then
      for n in env.header.moduleData[i]!.constNames do
        for a in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Disallowed {a} in {n}"
        count := count + 1
  if count == 0 then throwError "Empty audit of {mod}"
  logInfo m!"Audited {count} declarations in {mod}"
