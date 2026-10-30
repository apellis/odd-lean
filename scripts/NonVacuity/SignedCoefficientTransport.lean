import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.SignedCoefficientTransport
import Lean.Util.CollectAxioms
/-! Default-option arbitrary-data consumer of signed coefficient transport.
This is an API regression, not a constructed nonzero swapped representation. -/
noncomputable section
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
open OddMath.QuiverHecke.SwappedAssembly
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

/-- Signed single-edge coefficient transport between any two functor images of
mixed pairs. The hypotheses concern only the two dots, not the coefficient or
any braid. This includes whiskered and conjugated pairs through linear functors. -/
example (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (i : I) (s t : Sector I)
    (hs : StepValid (true, i) false s) (ht : StepValid (true, i) false t)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) false s)))
    (W : P.H (nextSector (true, i) true (nextSector (true, i) false t)))
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    (F : P.H s ⥤ C) [F.Additive] [F.Linear k]
    (G : P.H t ⥤ C) [G.Additive] [G.Linear k]
    (f : F.obj (P.rpObj i i s hs Z) ⟶ G.obj (P.rpObj i i t ht W))
    (ε : k) (hε : ε * ε = 1)
    (hx : F.map (P.rpPreDot i s hs Z) ≫ f =
      ε • (f ≫ G.map (P.rpPreDot i t ht W)))
    (hy : F.map (P.rpPostDot i s hs Z) ≫ f =
      ε • (f ≫ G.map (P.rpPostDot i t ht W))) :
    F.map (c.a i s hs Z) ≫ f = ε • (f ≫ G.map (c.a i t ht W)) :=
  c.signed_transport P hc h i s t hs ht Z W F G f ε hε hx hy
end ProbeReservoir

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.SignedCoefficientTransport
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
