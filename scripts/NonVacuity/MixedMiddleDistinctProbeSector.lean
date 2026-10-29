import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.MiddleDistinctProbeSector
import Lean.Util.CollectAxioms

/-! Three distinct colours and one occupied reservoir letter. The supplied
representation data and coefficients remain arbitrary; this is not an
independently nonzero representation. -/
noncomputable section
namespace NonVacuity.MixedMiddleDistinctProbeSector
open CategoryTheory StringDiagrams OddMath.SKM
open OddMath.QuiverHecke.SwappedAssembly
open OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
variable {I X : Type} [AddCommGroup X] {k : Type} [CommRing k]
  {B : Type} [BicategoryStruct.{0, 0} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
  (P : ProbeReservoir k B D Sc) (ν : X)
example (i j r : I) (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (β γ : I →₀ ℕ) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (Z : P.H (nextSector (true, r) false (nextSector (true, i) true
      (nextSector (true, j) true (β, γ + Finsupp.single r 1))))) :
    let s : Sector I := (β, γ + Finsupp.single r 1)
    let hv : StepValid (true, r) false s := by classical simp [StepValid, s]
    let hs : nextSector (true, r) false (nextSector (true, j) true (nextSector (true, i) true s)) =
        nextSector (true, r) false (nextSector (true, i) true (nextSector (true, j) true s)) := by
      simp only [nextSector, add_right_comm]
    braidLeft (P.swappedGens c L) i r j ν
      (distinctProbeMiddle ν i j r s hv hs) (distinctProbeMiddle ν j i r s hv rfl) Z =
    braidRight (P.swappedGens c L) i r j ν
      (distinctProbeMiddle ν i j r s hv hs) (distinctProbeMiddle ν j i r s hv rfl) Z := by
  dsimp only
  exact P.middleDistinctProbe_braid ν i j r _ _ c L hij hir hjr _ Z
#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.middleDistinctProbe_braid
end NonVacuity.MixedMiddleDistinctProbeSector

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods := #[`OddMath.QuiverHecke.SwappedAssembly.BraidMixed.MiddleDistinctProbeSector]
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
