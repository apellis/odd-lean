import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctReservoirSector
import Lean.Util.CollectAxioms

/-! Arbitrary occupied-content application of the forward reservoir sector braid.
This does not assert an independent nonzero representation. -/
noncomputable section
namespace NonVacuity.MixedDistinctReservoirForward
open CategoryTheory StringDiagrams OddMath.SKM
open OddMath.QuiverHecke.SwappedAssembly
open OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
variable {I X : Type} [AddCommGroup X] {k : Type} [CommRing k]
  {B : Type} [BicategoryStruct.{0, 0} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k} (P : ProbeReservoir k B D Sc)
example (ν : X) (i r q : I) (hir : i ≠ r) (hiq : i ≠ q) (hrq : r ≠ q)
    (β γ : I →₀ ℕ) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (Z : P.H (nextSector (true, r) false (nextSector (true, q) false
      (nextSector (true, i) true (β, γ + Finsupp.single r 1 + Finsupp.single q 1))))) :
    let s : Sector I := (β, γ + Finsupp.single r 1 + Finsupp.single q 1)
    let hr : StepValid (true, r) false s := by classical simp [StepValid, s, hrq]
    let hq : StepValid (true, q) false (nextSector (true, r) false s) := by
      classical simp [StepValid, nextSector, s, hrq.symm]
    let hq' : StepValid (true, q) false s := by classical simp [StepValid, s, hrq.symm]
    let hr' : StepValid (true, r) false (nextSector (true, q) false s) := by
      classical simp [StepValid, nextSector, s]
    let hsP : nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) =
        nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)) := by
      simp only [nextSector, tsub_right_comm]
    braidLeft (P.swappedGens c L) i r q ν
      (distinctReservoirSource ν i r q s hr hq hsP)
      (distinctReservoirTarget ν i q r s hq' hr' rfl) Z =
    braidRight (P.swappedGens c L) i r q ν
      (distinctReservoirSource ν i r q s hr hq hsP)
      (distinctReservoirTarget ν i q r s hq' hr' rfl) Z := by
  dsimp only
  exact P.distinctReservoir_braid ν i r q _ _ _ _ _ c L hir hiq hrq _ Z
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.distinctReservoir_braid
end NonVacuity.MixedDistinctReservoirForward

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mod := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctReservoirSector
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
