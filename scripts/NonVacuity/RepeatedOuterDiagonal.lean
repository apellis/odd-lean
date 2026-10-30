import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterDiagonal
import Lean.Util.CollectAxioms

/-! Default-option application to arbitrary supplied swapped data. -/
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
  (i j : I) (s : Sector I) (hR : StepValid (true, i) false s)
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

example (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    let x := P.repeatedOuterX i j s hR hs Z
    let y := P.repeatedOuterY i j s hR hs Z
    let z := P.repeatedOuterZ i j s hR hs Z
    ((P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).inv ≫
      P.mixedQ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z)) ≫
      (P.step (true, j) true s trivial).map
        (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)) ≫
      (P.mixedJ j i s hR ((P.step (true, i) true _ trivial).obj ((P.castH hs).obj Z))).hom) -
      ((P.step (true, i) false s hR).map
          (P.preCrossNe j i (nextSector (true, i) false s) hs Z) ≫
        c.a i s hR ((P.step (true, j) true _ trivial).obj Z) ≫
        P.repeatedOuterProbeBack i j s hR hs Z : End (P.rpObj i j s hR
          ((P.step (true, i) true
            (nextSector (true, i) false (nextSector (true, j) true s)) trivial).obj
              ((P.castH hs).obj Z)))) =
      (∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (x ^ (D.dn i j - 1 - a) * z ^ a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i),
        ∑ a ∈ Finset.range b,
          (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
            (x ^ (b - 1 - a) * y ^ d * z ^ a) := by
  exact P.repeatedOuterDiagonal_correction i j s hR hs Z c hc h hij

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.repeatedOuterDiagonal_correction

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterDiagonal
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
