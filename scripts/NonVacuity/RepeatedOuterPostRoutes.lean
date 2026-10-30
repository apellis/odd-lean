import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPostRoutes
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

namespace RepeatedOuterPost
open ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hj0 : StepValid (true, j) false s)
  (hi0 : StepValid (true, i) false (nextSector (true, j) false s))
  (Z : P.H (nextSector (true, i) false
    (nextSector (true, j) false (nextSector (true, i) true s))))

section Transport
variable (hi : StepValid (true, i) false s)
  (hj : StepValid (true, j) false (nextSector (true, i) false s))
  (hs : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) =
    nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)))
  (Y : P.H (nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s))))

include hi hj in
theorem RepeatedOuterPostRoutes_consumer (ν : X) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    HEq (braidRight (P.swappedGens c L) i j i ν
      (SPath.three true false false trivial hj0 hi0 hs)
      (SPath.three true false false trivial hj0 hi0 hs) Y)
      (-(coefficientAlg P i j s hj0 hi0 (hs ▸ Y)
        (c.a i (nextSector (true, j) false s) hi0 (hs ▸ Y)) ≫
        qExpr Sc (middleDot P i j s hj0 hi0 (hs ▸ Y))
          (innerDot P i j s hj0 hi0 (hs ▸ Y)) j i)) := by
  exact braidRight_coefficient P i j s hj0 hi0 hi hj hs Y ν c L hc h hij
end Transport

end RepeatedOuterPost
end OddMath.QuiverHecke.SwappedAssembly

#print axioms OddMath.QuiverHecke.SwappedAssembly.RepeatedOuterPost.RepeatedOuterPostRoutes_consumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPostRoutes
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
