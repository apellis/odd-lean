import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentPureProbe
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentMixedProbe
import Lean.Util.CollectAxioms

/-! Supplied-data applications at arbitrary pure-probe endpoints. No independent
nonzero model is constructed. The mixed module supplies path-sum reductions,
not the missing split-sector braid. -/
open CategoryTheory StringDiagrams OddMath.SKM
open OddMath.QuiverHecke.SwappedAssembly ProbeReservoir
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

example (P : ProbeReservoir k B D Sc) (ν : X) (i j : I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) {s t : Sector I}
    (e : nextSector (true, j) true (nextSector (true, i) true
      (nextSector (true, i) true s)) = t)
    (p : SPath (wd D ν [up i, up i, up j]) s t)
    (q : SPath (wd D ν [up j, up i, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i i j ν p q Z =
      braidRight (P.swappedGens c L) i i j ν p q Z :=
  P.adjacentPureProbe_iij ν i j s c L hij e p q Z

example (P : ProbeReservoir k B D Sc) (ν : X) (i j : I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) {s t : Sector I}
    (e : nextSector (true, j) true (nextSector (true, j) true
      (nextSector (true, i) true s)) = t)
    (p : SPath (wd D ν [up i, up j, up j]) s t)
    (q : SPath (wd D ν [up j, up j, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j j ν p q Z =
      braidRight (P.swappedGens c L) i j j ν p q Z :=
  P.adjacentPureProbe_ijj ν i j s c L hij e p q Z

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentPureProbe,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentMixedProbe]
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
