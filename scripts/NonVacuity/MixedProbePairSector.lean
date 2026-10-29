import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ProbePairSector

/-! A concrete colour and sector pattern for the mixed sector braid.
The representation data and the tail object are arbitrary; the reservoir
contains one letter of colour `true`, and both probes have colour `false`.
-/
noncomputable section
namespace NonVacuity.MixedProbePairSector
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
private def s : Sector Bool := (0, Finsupp.single true 1)
private theorem hv : StepValid (true, true) false s := by
  simp [StepValid, s]
example (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (Z : P.H (nextSector (true, true) false
      (nextSector (true, false) true (nextSector (true, false) true s)))) :
    braidLeft (P.swappedGens c L) false false true ν
      (probePairSource ν false true s hv) (probePairTarget ν false true s hv) Z =
    braidRight (P.swappedGens c L) false false true ν
      (probePairSource ν false true s hv) (probePairTarget ν false true s hv) Z :=
  P.probePair_braid ν false true s hv c L Z (by decide)
example : ¬(false = true ∧ false ≠ false) := by decide
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.probePair_braid
end NonVacuity.MixedProbePairSector
