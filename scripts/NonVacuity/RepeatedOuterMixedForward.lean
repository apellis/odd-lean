import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterMixedForward
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

variable (P : ProbeReservoir k B D Sc)
variable (G : P.Generators)
  (ν : X) (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

/-- The full forward off-diagonal left sum has one surviving route.
The middle equal crossing is the prescribed coefficient-square entry. -/
theorem repeatedOuter_forward_left_obligation (hij : i ≠ j) :
    let m : SPath (wd D ν [up i, up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three false true true hR trivial trivial hs
    let n : SPath (wd D ν [up i, up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three true true false trivial trivial hR rfl
    let a : SPath (wd D ν [up j, up i, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three true false true trivial hR trivial hs
    let b : SPath (wd D ν [up j, up i, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three true true false trivial trivial hR hs
    braidLeft G i j i ν m n Z =
      (crossEntry G ν [] i j [up i] m a Z ≫
        crossEntry G ν [up j] i i [] a b Z) ≫
          crossEntry G ν [] j i [up i] b n Z :=
  P.repeatedOuter_forward_left_route G ν i j s hR hs Z hij

/-- The full forward off-diagonal right sum has one surviving route. -/
theorem repeatedOuter_forward_right_obligation (hij : i ≠ j) :
    let m : SPath (wd D ν [up i, up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three false true true hR trivial trivial hs
    let n : SPath (wd D ν [up i, up j, up i]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three true true false trivial trivial hR rfl
    let a : SPath (wd D ν [up i, up i, up j]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three false true true hR trivial trivial rfl
    let b : SPath (wd D ν [up i, up i, up j]) s
      (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))) :=
      SPath.three true false true trivial hR trivial rfl
    braidRight G i j i ν m n Z =
      (crossEntry G ν [up i] j i [] m a Z ≫
        crossEntry G ν [] i i [up j] a b Z) ≫
          crossEntry G ν [up i] i j [] b n Z :=
  P.repeatedOuter_forward_right_route G ν i j s hR hs Z hij

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.repeatedOuter_forward_left_obligation
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.repeatedOuter_forward_right_obligation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterMixedForward
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

