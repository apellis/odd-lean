import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseBraid
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
    (p : SPath (wd D ν [up j, up i, up i]) (β, γ + Finsupp.single i 1)
      (nextSector (true, j) true (nextSector (true, i) true
        (nextSector (true, i) false (β, γ + Finsupp.single i 1)))))
    (q : SPath (wd D ν [up i, up i, up j]) (β, γ + Finsupp.single i 1)
      (nextSector (true, j) true (nextSector (true, i) true
        (nextSector (true, i) false (β, γ + Finsupp.single i 1)))))
    (Z : P.H (nextSector (true, j) true (nextSector (true, i) true
      (nextSector (true, i) false (β, γ + Finsupp.single i 1))))) :
    braidLeft (P.swappedGens c L) j i i ν p q Z =
      braidRight (P.swappedGens c L) j i i ν p q Z := by
  have hR : StepValid (true, i) false (β, γ + Finsupp.single i 1) := by
    classical
    simp [StepValid]
  exact P.adjacentReverse_braid ν i j _ hR c L hc h hij p q Z

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseTransport,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseCoefficient,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseRectangle,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseReduction,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseMatrix,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseBraid]
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
