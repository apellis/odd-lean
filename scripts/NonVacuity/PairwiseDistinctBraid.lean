import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.PairwiseDistinct
import Lean.Util.CollectAxioms

/-! Generic supplied-data consumer of the arbitrary-path braid equality.
This checks all source/target paths, not just canonical placements. It does not
construct an independent nonzero representation. -/

open CategoryTheory StringDiagrams OddMath.SKM
open OddMath.QuiverHecke.SwappedAssembly
open ProbeReservoir
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

example (P : ProbeReservoir k B D Sc) (ν : X) (i j r : I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j, up r]) s t)
    (q : SPath (wd D ν [up r, up j, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j r ν p q Z =
      braidRight (P.swappedGens c L) i j r ν p q Z :=
  P.braid_pairwiseDistinct ν i j r c L hij hir hjr p q Z

#print axioms ProbeReservoir.braid_pairwiseDistinct

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctPureProbeSector,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctPureReservoirSector,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.PairwiseDistinct]
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
