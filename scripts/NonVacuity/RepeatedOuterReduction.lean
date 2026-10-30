import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterReduction
import Lean.Util.CollectAxioms

noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (G : P.Generators)
  (ν : X) (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

example (hij : i ≠ j)
    (q : SPath (wd D ν [up i, up j, up i]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))) :
    let m : SPath (wd D ν [up i, up j, up i]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three false true true hR trivial trivial hs
    let a : SPath (wd D ν [up j, up i, up i]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) := SPath.three true false true trivial hR trivial hs
    let b : SPath (wd D ν [up j, up i, up i]) s (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) := SPath.three true true false trivial trivial hR hs
    braidLeft G i j i ν m q Z =
      (crossEntry G ν [] i j [up i] m a Z ≫ crossEntry G ν [up j] i i [] a a Z) ≫ crossEntry G ν [] j i [up i] a q Z +
      (crossEntry G ν [] i j [up i] m a Z ≫ crossEntry G ν [up j] i i [] a b Z) ≫ crossEntry G ν [] j i [up i] b q Z := by
  exact P.repeatedOuter_braidLeft_row G ν i j s hR hs Z hij q

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.repeatedOuter_braidLeft_row

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterReduction
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == owner then
      for name in env.header.moduleData[i]!.constNames do
        count := count + 1
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
  if count == 0 then
    throwError "Missing owned module {owner}"
  logInfo m!"{owner}: audited {count} declarations; standard axioms only"
