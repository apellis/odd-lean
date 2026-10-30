import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReservoirComparison
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
theorem adjacentReservoir_comparison_consumer (P : ProbeReservoir k B D Sc)
    (ν : X) (i j : I) (s : Sector I)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    (hj₀ : StepValid (true, j) false s)
    (hi₀ : StepValid (true, i) false (nextSector (true, j) false s))
    {t : Sector I}
    (e₀ : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (e₁ : nextSector (true, i) true (nextSector (true, i) false (nextSector (true, j) false s)) = t)
    (Z : P.H t) (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν
      (SPath.three true false false trivial hi hj e₀)
      (SPath.three false false true hj₀ hi₀ trivial e₁) Z =
    braidRight (P.swappedGens c L) i i j ν
      (SPath.three true false false trivial hi hj e₀)
      (SPath.three false false true hj₀ hi₀ trivial e₁) Z :=
  P.adjacentReservoir_comparison_braid_transport ν i j s hi hj hj₀ hi₀ e₀ e₁ Z c L hij

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.adjacentReservoir_comparison_consumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReservoirComparison
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