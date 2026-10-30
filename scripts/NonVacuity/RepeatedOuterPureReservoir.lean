import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPureReservoir
import Lean.Util.CollectAxioms

/-! Generic supplied-data applications at arbitrary reservoir content.
No independent nonzero representation is claimed. -/
noncomputable section
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
open OddMath.QuiverHecke.SwappedAssembly ProbeReservoir
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

example (P : ProbeReservoir k B D Sc)
    (i j : I) (hne : i ≠ j) (β : I →₀ ℕ) {a bi bj cij cii d : X}
    (hi : a + D.α i = bi) (hj : a + D.α j = bj)
    (hij : bi + D.α j = cij) (hji : bj + D.α i = cij)
    (hii : bi + D.α i = cii)
    (hd12 : cij + D.α i = d) (hd13 : cii + D.α j = d) {e : B} (Z : e ⟶ P.W.obj a) :
    let pi := homContentShift D i β
    let pj := homContentShift D j β
    (homParityShift (k := k) pi).map
      (resCore P.W j i pj pi hi hij hj hji Z ▷ P.W.E i hd12) ≫
      resCore P.W i i pi pi hji hd12 hji hd12
        ((homParityShift (k := k) pj).obj (Z ≫ P.W.E j hj)) ≫
      (homParityShift (k := k) pi).map
        (resCore P.W i j pi pj hj hji hi hij Z ▷ P.W.E i hd12) - (
    resCore P.W i j pi pj hij hd12 hii hd13
        ((homParityShift (k := k) pi).obj (Z ≫ P.W.E i hi)) ≫
      (homParityShift (k := k) pj).map
        (resCore P.W i i pi pi hi hii hi hii Z ▷ P.W.E j hd13) ≫
      resCore P.W j i pj pi hii hd13 hij hd12
        ((homParityShift (k := k) pi).obj (Z ≫ P.W.E i hi))) =
    -(sign k (homContentShift D i β * (D.parity j * D.parity i)) •
      ((reservoirTotalIso Z (P.W.E i hi) (P.W.E j hij) (P.W.E i hd12) pi pj pi).hom ≫
        Z ◁ P.repeatedOuterReservoirCorrection i j hi hij hd12 ≫
        (reservoirTotalIso Z (P.W.E i hi) (P.W.E j hij) (P.W.E i hd12) pi pj pi).inv)) := by
  exact P.repeatedOuterPureReservoir_factor_braid i j hne β hi hj hij hji hii hd12 hd13 Z

example (P : ProbeReservoir k B D Sc)
    (ν : X) (i j : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hne : i ≠ j)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    (hr : StepValid (true, i) false (nextSector (true, j) false
      (nextSector (true, i) false s)))
    (Z : P.H (nextSector (true, i) false (nextSector (true, j) false
      (nextSector (true, i) false s)))) :
    let p := distinctPureReservoirPath (D := D) ν i j i s hi hj hr rfl
    let Θ := reservoirTotalIso (k := k) Z (P.W.E i (P.muM_postE i hr))
      (P.W.E j (P.muM_postE j hj)) (P.W.E i (P.muM_postE i hi))
      (homContentShift D i s.1) (homContentShift D j s.1) (homContentShift D i s.1)
    HEq (braidLeft (P.swappedGens c L) i j i ν p p Z -
      braidRight (P.swappedGens c L) i j i ν p p Z)
      (sign k (homContentShift D i s.1 * (D.parity j * D.parity i)) •
        (Θ.hom ≫ Z ◁ P.repeatedOuterReservoirCorrection i j
          (P.muM_postE i hr) (P.muM_postE j hj) (P.muM_postE i hi) ≫ Θ.inv)) := by
  exact P.repeatedOuterPureReservoir_canonical_heq ν i j s c L hne hi hj hr Z

example (P : ProbeReservoir k B D Sc)
    (ν : X) (i j : I) {s t : Sector I} (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (ht : t.1 = s.1) (p q : SPath (wd D ν [up i, up j, up i]) s t)
    (hpq : p ≠ q) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j i ν p q Z = 0 ∧
      braidRight (P.swappedGens c L) i j i ν p q Z = 0 := by
  exact P.repeatedOuterPureReservoir_offdiag ν i j c L ht p q hpq Z

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPureReservoir]
  for owner in owners do
    let mut count : Nat := 0
    let mut privateCount : Nat := 0
    for i in [:env.header.moduleNames.size] do
      if env.header.moduleNames[i]! == owner then
        for name in env.header.moduleData[i]!.constNames do
          count := count + 1
          if name.getRoot == `_private then
            privateCount := privateCount + 1
          let axioms ← Lean.collectAxioms name
          for axiomName in axioms do
            unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
              throwError "Disallowed axiom {axiomName} in {name}"
    if count == 0 then
      throwError "Missing owned module {owner}"
    logInfo m!"{owner}: audited {count} declarations ({privateCount} private); standard axioms only"
