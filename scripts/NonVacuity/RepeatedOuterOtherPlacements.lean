import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterOtherPlacements
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
/-- A genuine mixed entry without coefficient inverse assumptions. -/
theorem repeatedOuter_reverse_offDiagonal_obligation
    (P : ProbeReservoir k B D Sc) (ν : X) (i j : I) (s : Sector I)
    (hR : StepValid (true, i) false s) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j)
    (hsR : nextSector (true, i) false (nextSector (true, j) true (nextSector (true, i) true s)) =
      nextSector (true, i) false (nextSector (true, i) true (nextSector (true, j) true s)))
    (Z : P.H (nextSector (true, i) false (nextSector (true, i) true (nextSector (true, j) true s)))) :
    braidLeft (P.swappedGens c L) i j i ν
      (distinctProbeSource ν i j i s hR hsR) (distinctProbeTarget ν j i i s hR rfl) Z =
    braidRight (P.swappedGens c L) i j i ν
      (distinctProbeSource ν i j i s hR hsR) (distinctProbeTarget ν j i i s hR rfl) Z :=
  P.repeatedOuter_other_offDiag ν i j s hR c L hij hsR Z

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.repeatedOuter_other_offDiag
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.repeatedOuter_reverse_offDiagonal_obligation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterOtherPlacements
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
