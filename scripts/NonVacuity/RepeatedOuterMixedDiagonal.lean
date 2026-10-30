import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterMixedDiagonal
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
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hR : StepValid (true, i) false s)
  (hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
    nextSector (true, j) true (nextSector (true, i) true s))
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

/-- With explicit sign normalizations, the single edge has the Koszul sign.
The source normalization is `(-1)^pᵢ`, and the separated target normalization
is `(-1)^(pᵢ+pᵢpⱼ)`. Both total parities are retained. -/
theorem repeatedOuterMixed_signed_edge_obligation (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    (zsign k (D.parity i) • P.repeatedOuterMixedAdjacentCoeff i j s hR hs Z c) ≫
        P.adjacentReverseProbeCross i j s hR hs₀ Z =
      zsign k (D.parity i * D.parity j) •
        (P.adjacentReverseProbeCross i j s hR hs₀ Z ≫
          ((zsign k (D.parity i * D.parity j) * zsign k (D.parity i)) •
            P.repeatedOuterMixedSeparatedCoeff i j s hR Z c)) :=
  P.repeatedOuterMixed_probe_coeff_signed i j s hR hs₀ hs Z c hc h hij

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.repeatedOuterMixed_signed_edge_obligation

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterMixedDiagonal
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
