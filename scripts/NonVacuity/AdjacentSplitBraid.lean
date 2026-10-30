import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentMixedRectangle
import Lean.Util.CollectAxioms

/-! Generic supplied-data application at arbitrary occupied reservoir content.
No independent nonzero representation is claimed. -/
noncomputable section
open CategoryTheory StringDiagrams OddMath.SKM
open OddMath.QuiverHecke.SwappedAssembly ProbeReservoir
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

example (P : ProbeReservoir k B D Sc) (ν : X) (i j : I) (hij : i ≠ j)
    (β γ : I →₀ ℕ) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs)
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) false (β, γ + Finsupp.single i 1))))) :
    let s : Sector I := (β, γ + Finsupp.single i 1)
    let hR : StepValid (true, i) false s := by classical simp [StepValid, s]
    let hs : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) =
      nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) := by
        simp only [nextSector, add_right_comm]
    braidLeft (P.swappedGens c L) i i j ν
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three true false true trivial hR trivial rfl) Z =
    braidRight (P.swappedGens c L) i i j ν
      (SPath.three false true true hR trivial trivial hs)
      (SPath.three true false true trivial hR trivial rfl) Z := by
  dsimp only
  exact P.adjacentMixed_braid ν i j _ _ c L _ Z hc h hij

#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.adjacentMixed_braid
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.adjacentMixed_J_rectangle

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentMixedTransport,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentMixedCoefficient,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentMixedBraid,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentMixedRectangle]
  for owner in owners do
    let mut count : Nat := 0
    let mut privateCount : Nat := 0
    for i in [:env.header.moduleNames.size] do
      if env.header.moduleNames[i]! == owner then
        for name in env.header.moduleData[i]!.constNames do
          count := count + 1
          if name.getRoot == `_private then
            privateCount := privateCount + 1
          let axioms ← Lean.collectAxioms name
          for axiomName in axioms do
            unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
              throwError "Disallowed axiom {axiomName} in {name}"
    if count == 0 then
      throwError "Missing owned module {owner}"
    logInfo m!"{owner}: audited {count} declarations ({privateCount} private); standard axioms only"
