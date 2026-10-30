import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPureProbe
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
    (i j : I) (hne : i ≠ j) {a bi bj cij cii d : X}
    (hi : a + D.α i = bi) (hj : a + D.α j = bj)
    (hij : bi + D.α j = cij) (hji : bj + D.α i = cij)
    (hii : bi + D.α i = cii)
    (hd12 : cij + D.α i = d) (hd13 : cii + D.α j = d) {e : B} (Z : P.T.obj d ⟶ e) :
    ((associator (P.T.E i hi) (P.T.E j hij) ((P.T.E i hd12) ≫ Z)).inv ≫ (P.T.cross j i hi hij hj
        hji) ▷ ((P.T.E i hd12) ≫ Z) ≫ (associator (P.T.E j hj) (P.T.E i hji) ((P.T.E i hd12) ≫
        Z)).hom) ≫
      (P.T.E j hj) ◁ ((associator (P.T.E i hji) (P.T.E i hd12) Z).inv ≫ (P.T.cross i i hji hd12
          hji hd12) ▷ Z ≫ (associator (P.T.E i hji) (P.T.E i hd12) Z).hom) ≫
      ((associator (P.T.E j hj) (P.T.E i hji) ((P.T.E i hd12) ≫ Z)).inv ≫ (P.T.cross i j hj hji hi
          hij) ▷ ((P.T.E i hd12) ≫ Z) ≫ (associator (P.T.E i hi) (P.T.E j hij) ((P.T.E i hd12) ≫
          Z)).hom) - (
      (P.T.E i hi) ◁ ((associator (P.T.E j hij) (P.T.E i hd12) Z).inv ≫ (P.T.cross i j hij hd12
          hii hd13) ▷ Z ≫ (associator (P.T.E i hii) (P.T.E j hd13) Z).hom) ≫
      ((associator (P.T.E i hi) (P.T.E i hii) ((P.T.E j hd13) ≫ Z)).inv ≫ (P.T.cross i i hi hii hi
          hii) ▷ ((P.T.E j hd13) ≫ Z) ≫ (associator (P.T.E i hi) (P.T.E i hii) ((P.T.E j hd13) ≫
          Z)).hom) ≫
      (P.T.E i hi) ◁ ((associator (P.T.E i hii) (P.T.E j hd13) Z).inv ≫ (P.T.cross j i hii hd13
          hij hd12) ▷ Z ≫ (associator (P.T.E j hij) (P.T.E i hd12) Z).hom) ) =
      -((tripleRightIso (k := k) (P.T.E i hi) (P.T.E j hij) (P.T.E i hd12) Z).inv ≫
        P.repeatedOuterProbeCorrection i j hi hij hd12 ▷ Z ≫
        (tripleRightIso (k := k) (P.T.E i hi) (P.T.E j hij) (P.T.E i hd12) Z).hom) := by
  exact P.repeatedOuterPureProbe_factor_braid i j hne hi hj hij hji hii hd12 hd13 Z

example (P : ProbeReservoir k B D Sc)
    (i j : I) (hne : i ≠ j) {a bi bj cij cii d : X}
    (hi : a + D.α i = bi) (hj : a + D.α j = bj)
    (hij : bi + D.α j = cij) (hji : bj + D.α i = cij)
    (hii : bi + D.α i = cii) (hd12 : cij + D.α i = d)
    (hd13 : cii + D.α j = d) {e : B} (Z : P.T.obj d ⟶ e) :
    probeCore P.T i j hi hij hj hji (P.T.E i hd12 ≫ Z) ≫
      P.T.E j hj ◁ (pureProbeScale (D := D) i i •
        probeCore P.T i i hji hd12 hji hd12 Z) ≫
      probeCore P.T j i hj hji hi hij (P.T.E i hd12 ≫ Z) -
    (P.T.E i hi ◁ probeCore P.T j i hij hd12 hii hd13 Z ≫
      (pureProbeScale (D := D) i i •
        probeCore P.T i i hi hii hi hii (P.T.E j hd13 ≫ Z)) ≫
      P.T.E i hi ◁ probeCore P.T i j hii hd13 hij hd12 Z) =
    koszulSign (D.parity i) (D.parity i) •
      ((tripleRightIso (k := k) (P.T.E i hi) (P.T.E j hij) (P.T.E i hd12) Z).inv ≫
        P.repeatedOuterProbeCorrection i j hi hij hd12 ▷ Z ≫
        (tripleRightIso (k := k) (P.T.E i hi) (P.T.E j hij) (P.T.E i hd12) Z).hom) := by
  exact P.repeatedOuterPureProbe_scaled_factor_braid i j hne hi hj hij hji hii hd12 hd13 Z

example
    (P : ProbeReservoir k B D Sc) (ν : X) (i j : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hne : i ≠ j)
    (Z : P.H (nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) true s)))) :
    let p := distinctPureProbePath (D := D) ν i j i s rfl
    let Θ := tripleRightIso (k := k) (P.T.E i (P.muP_preE i s))
      (P.T.E j (P.muP_preE j _)) (P.T.E i (P.muP_preE i _)) Z
    HEq (braidLeft (P.swappedGens c L) i j i ν p p Z -
      braidRight (P.swappedGens c L) i j i ν p p Z)
      (koszulSign (D.parity i) (D.parity i) •
        (Θ.inv ≫ P.repeatedOuterProbeCorrection i j
          (P.muP_preE i s) (P.muP_preE j _) (P.muP_preE i _) ▷ Z ≫ Θ.hom)) := by
  exact P.repeatedOuterPureProbe_canonical_heq ν i j s c L hne Z

example
    (P : ProbeReservoir k B D Sc)
    (ν : X) (i j : I) {s t : Sector I} (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (ht : nextSector (true, i) true (nextSector (true, j) true
      (nextSector (true, i) true s)) = t) (p q : SPath (wd D ν [up i, up j, up i]) s t)
    (hpq : p ≠ q) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j i ν p q Z = 0 ∧
      braidRight (P.swappedGens c L) i j i ν p q Z = 0 := by
  exact P.repeatedOuterPureProbe_offdiag ν i j c L ht p q hpq Z

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPureProbe]
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
