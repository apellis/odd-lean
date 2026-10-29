import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReservoirPairSector

/-! The complementary mixed sector braid with two reservoir letters.
The representation data are arbitrary. The concrete sector supplies both
reservoir validity proofs, and the two Boolean colours are distinct.
-/
noncomputable section
namespace NonVacuity.MixedReservoirPairSector
open CategoryTheory StringDiagrams OddMath.SKM
open OddMath.QuiverHecke.SwappedAssembly
open OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
variable {X : Type} [AddCommGroup X] {k : Type} [CommRing k]
  {B : Type} [BicategoryStruct.{0, 0} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum Bool X} {Sc : Scalars D k}
  (P : ProbeReservoir k B D Sc) (ν : X)
private def s : Sector Bool := (0, Finsupp.single true 2)
private theorem hv : StepValid (true, true) false s := by
  simp [StepValid, s]
private theorem hw : StepValid (true, true) false (nextSector (true, true) false s) := by
  simp [StepValid, nextSector, s]
example (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (Z : P.H (nextSector (true, true) false
      (nextSector (true, true) false (nextSector (true, false) true s)))) :
    braidLeft (P.swappedGens c L) false true true ν
      (reservoirPairSource ν false true s hv hw) (reservoirPairTarget ν false true s hv hw) Z =
    braidRight (P.swappedGens c L) false true true ν
      (reservoirPairSource ν false true s hv hw) (reservoirPairTarget ν false true s hv hw) Z :=
  P.reservoirPair_braid ν false true s hv hw c L Z (by decide)
example : ¬(false = true ∧ false ≠ true) := by decide
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.reservoirPair_braid
end NonVacuity.MixedReservoirPairSector
