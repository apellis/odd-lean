import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterMiddleReservoir
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
variable (ν : X) (i j : I) (s : Sector I) (hR : StepValid (true, j) false s)
  (c : P.CrossCoeff Sc) (L : P.LeftwardData)
include hR in
/-- The complete PRP diagonal correction at arbitrary terminal sectors and paths. -/
theorem middleReservoir_diagonal_consumer {t : Sector I}
    (e : nextSector (true, j) false (nextSector (true, i) true (nextSector (true, i) true s)) = t)
    (W : P.H t) (p : SPath (wd D ν [up i, up j, up i]) s t) (hij : i ≠ j) :
    braidLeft (P.swappedGens c L) i j i ν p p W -
      braidRight (P.swappedGens c L) i j i ν p p W =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p W) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p W) (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p W) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] p W) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p W) (b - 1 - a)) :=
  P.middleReservoir_braidEq_diag_transport ν i j s hR c L e W p hij

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.middleReservoir_diagonal_consumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterMiddleReservoir
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