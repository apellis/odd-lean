import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ProbePairDots

/-! The two transported Q factors have the same spectator dot.
Concrete colours and a valid occupied reservoir sector; representation data stay arbitrary. -/
noncomputable section
namespace NonVacuity.MixedProbePairDots
open CategoryTheory StringDiagrams OddMath.SKM
open OddMath.QuiverHecke.SwappedAssembly
open OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
variable {X : Type} [AddCommGroup X] {k : Type} [CommRing k]
  {B : Type} [BicategoryStruct.{0, 0} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum Bool X} {Sc : Scalars D k}
  (P : ProbeReservoir k B D Sc)
private def s : Sector Bool := (0, Finsupp.single true 1)
private theorem hv : StepValid (true, true) false s := by simp [StepValid, s]
example (Z : P.H (nextSector (true, true) false
      (nextSector (true, false) true (nextSector (true, false) true s)))) :
    ((P.probePairFirstIso false true s hv Z).hom ≫
      P.mixedQ false true s hv ((P.step (true, false) true
        (nextSector (true, true) false (nextSector (true, false) true s)) trivial).obj Z) ≫
      (P.probePairFirstIso false true s hv Z).inv) ≫
      (P.step (true, false) true s trivial).map
        (P.mixedQ false true (nextSector (true, false) true s) hv Z) =
    qExpr Sc (P.ppLeftDot false s ((P.step (true, true) false
      (nextSector (true, false) true (nextSector (true, false) true s)) hv).obj Z))
      (P.probePairSpectatorDot false true s hv Z) false true ≫
    qExpr Sc (P.ppRightDot false s ((P.step (true, true) false
      (nextSector (true, false) true (nextSector (true, false) true s)) hv).obj Z))
      (P.probePairSpectatorDot false true s hv Z) false true := by
  rw [P.probePairFirstIso_conj_mixedQ, P.probePair_map_mixedQ]
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.ppLeftDot_comp_probePairSpectatorDot
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.ppRightDot_comp_probePairSpectatorDot
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.preCrossSame_comp_probePairSpectatorDot
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.probePair_map_mixedQ
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.ppLeftDot_comp_probePairFirstIso
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.probePairFirstIso_conj_prPostDot
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.probePairFirstIso_conj_mixedQ
end NonVacuity.MixedProbePairDots
