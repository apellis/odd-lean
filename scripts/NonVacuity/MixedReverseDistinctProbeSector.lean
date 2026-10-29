import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReverseDistinctProbeSector
import Lean.Util.CollectAxioms

/-! Three distinct colours and one occupied reservoir letter. The supplied
representation data and coefficients remain arbitrary; this is not an
independently nonzero representation. -/
noncomputable section
namespace NonVacuity.MixedReverseDistinctProbeSector
open CategoryTheory StringDiagrams OddMath.SKM
open OddMath.QuiverHecke.SwappedAssembly
open OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
variable {X : Type} [AddCommGroup X] {k : Type} [CommRing k]
  {B : Type} [BicategoryStruct.{0, 0} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum (Fin 3) X} {Sc : Scalars D k}
  (P : ProbeReservoir k B D Sc) (ν : X)
private def s : Sector (Fin 3) := (0, Finsupp.single 2 1)
private theorem hv : StepValid (true, (2 : Fin 3)) false s := by
  simp [StepValid, s]
private theorem hs :
    nextSector (true, (2 : Fin 3)) false (nextSector (true, 1) true (nextSector (true, 0) true s)) =
      nextSector (true, 2) false (nextSector (true, 0) true (nextSector (true, 1) true s)) := by
  simp only [nextSector, add_right_comm]
example (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (Z : P.H (nextSector (true, (2 : Fin 3)) false
      (nextSector (true, 0) true (nextSector (true, 1) true s)))) :
    braidLeft (P.swappedGens c L) 2 0 1 ν
      (distinctProbeTarget ν 0 1 2 s hv hs) (distinctProbeSource ν 1 0 2 s hv rfl) Z =
    braidRight (P.swappedGens c L) 2 0 1 ν
      (distinctProbeTarget ν 0 1 2 s hv hs) (distinctProbeSource ν 1 0 2 s hv rfl) Z :=
  P.reverseDistinctProbe_braid ν 0 1 2 s hv c L (by decide) (by decide) (by decide) hs Z
example : ¬((2 : Fin 3) = 1 ∧ (2 : Fin 3) ≠ 0) := by decide
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.reverseDistinctProbe_braid
end NonVacuity.MixedReverseDistinctProbeSector

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods := #[
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctQTransport,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctProbeDots,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctProbeQ,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReverseDistinctProbeEdges,
    `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReverseDistinctProbeSector]
  for mod in mods do
    let mut count : Nat := 0
    for i in [:env.header.moduleNames.size] do
      if env.header.moduleNames[i]! == mod then
        for n in env.header.moduleData[i]!.constNames do
          for a in (← Lean.collectAxioms n) do
            unless #[`propext, `Classical.choice, `Quot.sound].contains a do
              throwError "Disallowed {a} in {n}"
          count := count + 1
    if count == 0 then throwError "Empty audit of {mod}"
    logInfo m!"Audited {count} declarations in {mod}"
