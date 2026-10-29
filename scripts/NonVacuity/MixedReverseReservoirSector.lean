import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReverseReservoirSector
import Lean.Util.CollectAxioms

/-! The reverse Q-weighted sector braid with two reservoir letters.
The representation data are arbitrary. The concrete sector supplies both
reservoir validity proofs, and the two Boolean colours are distinct.
This is an occupied-sector theorem application, not a nonzero model construction.
-/
noncomputable section
namespace NonVacuity.MixedReverseReservoirSector
open CategoryTheory StringDiagrams OddMath.SKM
open OddMath.QuiverHecke.SwappedAssembly
open OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
variable {X : Type} [AddCommGroup X] {k : Type} [CommRing k]
  {B : Type} [BicategoryStruct.{0, 0} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum Bool X} {Sc : Scalars D k}
  (P : ProbeReservoir k B D Sc) (ν : X)
private def s : Sector Bool := (0, Finsupp.single true 2)
private theorem hv : StepValid (true, true) false s := by
  simp [StepValid, s]
private theorem hw : StepValid (true, true) false (nextSector (true, true) false s) := by
  simp [StepValid, nextSector, s]
example (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (Z : P.H (nextSector (true, true) false
      (nextSector (true, true) false (nextSector (true, false) true s)))) :
    braidLeft (P.swappedGens c L) true true false ν
      (reservoirPairTarget ν false true s hv hw) (reservoirPairSource ν false true s hv hw) Z =
    braidRight (P.swappedGens c L) true true false ν
      (reservoirPairTarget ν false true s hv hw) (reservoirPairSource ν false true s hv hw) Z :=
  P.reverseReservoirPair_braid ν false true s hv hw c L Z (by decide)
example : ¬(false = true ∧ false ≠ true) := by decide
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.reverseReservoirPair_braid
end NonVacuity.MixedReverseReservoirSector

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReservoirPairDots,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReservoirPairQCentrality,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReverseReservoirSector]
  for mod in modules do
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
