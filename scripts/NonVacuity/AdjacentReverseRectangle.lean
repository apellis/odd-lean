import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseRectangle
import Lean.Util.CollectAxioms

/-! Default-option applications of the reverse split coefficient and comparison
rectangles. These use arbitrary supplied data, not an independently constructed
nonzero representation. -/
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
variable (P : ProbeReservoir k B D Sc) (c : P.CrossCoeff Sc)
  (hc : c.IsInverse) (h : P.CrossCoeffInputs) (i j : I) (s : Sector I)
  (hR : StepValid (true, i) false s)
  (hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
    nextSector (true, j) true (nextSector (true, i) true s))
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

include hc h in
example (hij : i ≠ j) :
    (P.step (true, j) true s trivial).map
        (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)) ≫
      P.adjacentReverseMove i j s hR hs Z =
    P.adjacentReverseMove i j s hR hs Z ≫
      c.a i s hR ((P.step (true, j) true _ trivial).obj Z) :=
  P.adjacentReverseMove_coeff c hc h i j s hR hs Z hij

example :
    (P.step (true, j) true s trivial).map
        (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).hom ≫
      P.adjacentReverseMove i j s hR hs Z =
    P.adjacentReverseProbeCross i j s hR hs₀ Z ≫
      (P.step (true, i) true s trivial).map
        (P.mixedJ j i (nextSector (true, i) true s) hR Z).hom ≫
      (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)).hom :=
  P.adjacentReverse_J_rectangle i j s hR hs₀ hs Z

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseTransport,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseCoefficient,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseRectangle]
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
