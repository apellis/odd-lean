import OddMath.QuiverHecke.SwappedAssembly.BraidAssembly
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

theorem crossBraid_consumer (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) : CrossBraid (P.swappedGens c L) :=
  P.crossBraidOfInputs c L hc h

theorem layerBraid_consumer (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) {Gs Ys : ∀ s, P.H s} :
    BraidRelations Sc (P.layerRep Gs Ys (P.swappedGens c L)) :=
  P.braidRelationsOfInputs c L hc h

example (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) :=
  (P.crossBraidOfInputs c L hc h).braid

example (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) :=
  (P.crossBraidOfInputs c L hc h).braidEq_offDiag

example (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) :=
  (P.crossBraidOfInputs c L hc h).braidEq_diag
theorem offDiagonal_consumer (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (i j : I) (ν : X) (hij : i ≠ j)
    {s t : Sector I} (p q : SPath (wd D ν [up i, up j, up i]) s t)
    (Z : P.H t) (hpq : p ≠ q) :
    braidLeft (P.swappedGens c L) i j i ν p q Z =
      braidRight (P.swappedGens c L) i j i ν p q Z :=
  (P.crossBraidOfInputs c L hc h).braidEq_offDiag i j ν hij p q Z hpq

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.crossBraid_consumer
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.layerBraid_consumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidAssembly
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
