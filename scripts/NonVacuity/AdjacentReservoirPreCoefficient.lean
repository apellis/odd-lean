import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReservoirPreCoefficient
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
namespace AdjacentReservoirPreCoefficient
open ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hi : StepValid (true, i) false s)
  (hj : StepValid (true, j) false (nextSector (true, i) false s))
  (hj0 : StepValid (true, j) false s)
  (hi0 : StepValid (true, i) false (nextSector (true, j) false s))

theorem adjacent_coefficient_consumer (ν : X) {t : Sector I}
    (e : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t)
    (e' : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t)
    (Z : P.H t) (p : SPath (wd D ν [up i, up i, up j]) s t)
    (q : SPath (wd D ν [up j, up i, up i]) s t)
    (hp : p = SPath.three (c₁ := ⟨up i, SKM.wt D ν [up i, up j]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up j]⟩) (c₃ := ⟨up j, ν⟩)
      false true false hi trivial hj e)
    (hq : q = SPath.three (c₁ := ⟨up j, SKM.wt D ν [up i, up i]⟩)
      (c₂ := ⟨up i, SKM.wt D ν [up i]⟩) (c₃ := ⟨up i, ν⟩)
      false false true hj0 hi0 trivial e')
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i i j ν p q Z =
      braidRight (P.swappedGens c L) i i j ν p q Z := by
  exact braid_entry_path P i j s hi hj hj0 hi0 ν e e' Z p q hp hq c L hc h hij
end AdjacentReservoirPreCoefficient
end OddMath.QuiverHecke.SwappedAssembly
#print axioms OddMath.QuiverHecke.SwappedAssembly.AdjacentReservoirPreCoefficient.adjacent_coefficient_consumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReservoirPreCoefficient
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
