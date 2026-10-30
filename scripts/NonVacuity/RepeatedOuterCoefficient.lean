import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterCoefficient
import Lean.Util.CollectAxioms
/-! Default-option application to arbitrary supplied swapped data; not an
independent nonzero representation. -/
noncomputable section
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
open OddMath.QuiverHecke.SwappedAssembly
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (c : P.CrossCoeff Sc)
  (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

example (hc : c.IsInverse) (h : P.CrossCoeffInputs)
    (hij : i ≠ j) :
    (P.step (true, i) false s hR).map
        (P.preCrossNe j i (nextSector (true, i) false s) hs Z) ≫
      c.a i s hR ((P.step (true, j) true _ trivial).obj Z) =
    zsign k (D.parity i * D.parity j) •
      (P.repeatedOuterProbeCoeff c i j s hR hs Z ≫
        (P.step (true, i) false s hR).map
          (P.preCrossNe j i (nextSector (true, i) false s) hs Z)) :=
  P.repeatedOuterProbeCross_coeff c i j s hR hs Z hc h hij
end ProbeReservoir

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterCoefficient
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
