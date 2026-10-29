import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ProbePairQCentrality

import Lean.Util.CollectAxioms

/-! The two transported Q factors have the same spectator dot.
Concrete colours and a valid occupied reservoir sector; representation data stay arbitrary. -/
noncomputable section
namespace NonVacuity.MixedProbePairQCentrality
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
    Commute
      (P.preCrossSame false s ((P.step (true, true) false
        (nextSector (true, false) true (nextSector (true, false) true s)) hv).obj Z))
      (((P.probePairFirstIso false true s hv Z).hom ≫
        P.mixedQ false true s hv ((P.step (true, false) true
          (nextSector (true, true) false (nextSector (true, false) true s)) trivial).obj Z) ≫
        (P.probePairFirstIso false true s hv Z).inv) ≫
        (P.step (true, false) true s trivial).map
          (P.mixedQ false true (nextSector (true, false) true s) hv Z)) :=
  probePairQProduct_central Sc P false true s hv Z
end NonVacuity.MixedProbePairQCentrality

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in #[
      `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.QWeightedPolynomial,
      `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.QWeightedEvaluation,
      `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.QCentralRealization,
      `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ProbePairQCentrality] do
    let mut count : Nat := 0
    for i in [:env.header.moduleNames.size] do
      if env.header.moduleNames[i]! == mod then
        for n in env.header.moduleData[i]!.constNames do
          for a in (← Lean.collectAxioms n) do
            unless #[`propext, `Classical.choice, `Quot.sound].contains a do
              throwError "Disallowed {a} in {n}"
          count := count + 1
    if count == 0 then throwError "Empty audit for {mod}"
    logInfo m!"Audited {count} declarations in {mod}"
