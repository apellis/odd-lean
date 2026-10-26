import OddMath.SKM.RouquierHomReservoirPowers
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierHomReservoirPowers
private def D : Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two

variable {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
  [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
  [∀ a b : B, PiSupercategory ℚ (a ⟶ b)]
  (T : RouquierFamily (k := ℚ) (B := B) D) (W : ℤ → B)

private theorem edge : -(0 : ℤ) + D.α () = -(-2) := by simp [D, Datum.α]

variable (muM muP nuP : ℤ) (h : -nuP + D.α () = -muP)

example (n : ℕ) (Z : homWeightSector T.obj W muP muM) :
    homReservoirCup T W () muM h n Z ≫
      ((homParityShiftDatum (k := ℚ) (leftAdjParity D () (-nuP))).iso
        (T.F () h ≫ T.E () h ≫ Z)).hom =
    koszulSign (leftAdjParity D () (-nuP)) ((n : ZMod 2) * D.parity ()) •
      ((leftUnitor Z).inv ≫ T.leftCup () h ▷ Z ≫
        (associator (T.F () h) (T.E () h) Z).hom ≫
        T.F () h ◁ (rouquierPower (T.dot () h) n ▷ Z)) :=
  homReservoirCup_coordinates T W () muM h n Z

example (Z : homWeightSector T.obj W (-2) muM) :
    homReservoirCup T W () muM edge 0 Z ≫
      ((homParityShiftDatum (k := ℚ) (leftAdjParity D () (-0))).iso
        (T.F () edge ≫ T.E () edge ≫ Z)).hom =
    koszulSign (leftAdjParity D () (-0)) ((0 : ZMod 2) * D.parity ()) •
      ((leftUnitor Z).inv ≫ T.leftCup () edge ▷ Z ≫
        (associator (T.F () edge) (T.E () edge) Z).hom ≫
        T.F () edge ◁ (rouquierPower (T.dot () edge) 0 ▷ Z)) :=
  homReservoirCup_coordinates T W () muM edge 0 Z

example (Z : homWeightSector T.obj W (-2) muM) :
    homReservoirCup T W () muM edge 1 Z ≫
      ((homParityShiftDatum (k := ℚ) (leftAdjParity D () (-0))).iso
        (T.F () edge ≫ T.E () edge ≫ Z)).hom =
    koszulSign (leftAdjParity D () (-0)) ((1 : ZMod 2) * D.parity ()) •
      ((leftUnitor Z).inv ≫ T.leftCup () edge ▷ Z ≫
        (associator (T.F () edge) (T.E () edge) Z).hom ≫
        T.F () edge ◁ (rouquierPower (T.dot () edge) 1 ▷ Z)) :=
  homReservoirCup_coordinates T W () muM edge 1 Z

example (Z : homWeightSector T.obj W (-2) muM) :
    homReservoirCup T W () muM edge 2 Z ≫
      ((homParityShiftDatum (k := ℚ) (leftAdjParity D () (-0))).iso
        (T.F () edge ≫ T.E () edge ≫ Z)).hom =
    koszulSign (leftAdjParity D () (-0)) ((2 : ZMod 2) * D.parity ()) •
      ((leftUnitor Z).inv ≫ T.leftCup () edge ▷ Z ≫
        (associator (T.F () edge) (T.E () edge) Z).hom ≫
        T.F () edge ◁ (rouquierPower (T.dot () edge) 2 ▷ Z)) :=
  homReservoirCup_coordinates T W () muM edge 2 Z

example (n : ℕ) (Z : homWeightSector T.obj W nuP muM) :
    homReservoirCap T W () muM h n Z =
    koszulSign (leftAdjParity D () (-nuP))
      (1 + (n : ZMod 2) * D.parity ()) •
      (T.E () h ◁ ((homParityShiftDatum (k := ℚ) (leftAdjParity D () (-nuP))).iso
        (T.F () h ≫ Z)).hom ≫
        rouquierPower (T.dot () h) n ▷ (T.F () h ≫ Z) ≫
        (associator (T.E () h) (T.F () h) Z).inv ≫
        ((((T.leftAdjScalar () (-nuP))⁻¹ : ℚˣ) : ℚ) • T.leftCap () h) ▷ Z ≫
        (leftUnitor Z).hom) :=
  homReservoirCap_coordinates T W () muM h n Z

example (Z : homWeightSector T.obj W 0 muM) :
    homReservoirCap T W () muM edge 0 Z =
    koszulSign (leftAdjParity D () (-0))
      (1 + (0 : ZMod 2) * D.parity ()) •
      (T.E () edge ◁ ((homParityShiftDatum (k := ℚ) (leftAdjParity D () (-0))).iso
        (T.F () edge ≫ Z)).hom ≫
        rouquierPower (T.dot () edge) 0 ▷ (T.F () edge ≫ Z) ≫
        (associator (T.E () edge) (T.F () edge) Z).inv ≫
        ((((T.leftAdjScalar () (-0))⁻¹ : ℚˣ) : ℚ) • T.leftCap () edge) ▷ Z ≫
        (leftUnitor Z).hom) :=
  homReservoirCap_coordinates T W () muM edge 0 Z

example (Z : homWeightSector T.obj W 0 muM) :
    homReservoirCap T W () muM edge 1 Z =
    koszulSign (leftAdjParity D () (-0))
      (1 + (1 : ZMod 2) * D.parity ()) •
      (T.E () edge ◁ ((homParityShiftDatum (k := ℚ) (leftAdjParity D () (-0))).iso
        (T.F () edge ≫ Z)).hom ≫
        rouquierPower (T.dot () edge) 1 ▷ (T.F () edge ≫ Z) ≫
        (associator (T.E () edge) (T.F () edge) Z).inv ≫
        ((((T.leftAdjScalar () (-0))⁻¹ : ℚˣ) : ℚ) • T.leftCap () edge) ▷ Z ≫
        (leftUnitor Z).hom) :=
  homReservoirCap_coordinates T W () muM edge 1 Z

example (Z : homWeightSector T.obj W 0 muM) :
    homReservoirCap T W () muM edge 2 Z =
    koszulSign (leftAdjParity D () (-0))
      (1 + (2 : ZMod 2) * D.parity ()) •
      (T.E () edge ◁ ((homParityShiftDatum (k := ℚ) (leftAdjParity D () (-0))).iso
        (T.F () edge ≫ Z)).hom ≫
        rouquierPower (T.dot () edge) 2 ▷ (T.F () edge ≫ Z) ≫
        (associator (T.E () edge) (T.F () edge) Z).inv ≫
        ((((T.leftAdjScalar () (-0))⁻¹ : ℚˣ) : ℚ) • T.leftCap () edge) ▷ Z ≫
        (leftUnitor Z).hom) :=
  homReservoirCap_coordinates T W () muM edge 2 Z

example : leftAdjParity D () 0 = 1 := by norm_num [leftAdjParity, D, Datum.h]
example : (List.map (fun n : ℕ => koszulSign (1 : ZMod 2) (n : ZMod 2)) [0,1,2]) = [1,-1,1] := by decide
example : (List.map (fun n : ℕ => koszulSign (1 : ZMod 2) (1 + (n : ZMod 2))) [0,1,2]) = [-1,1,-1] := by decide
end NonVacuity.RouquierHomReservoirPowers

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in #[`OddMath.SKM.RouquierHomReservoirPowers] do
    let mut count : Nat := 0
    for i in [:env.header.moduleNames.size] do
      if env.header.moduleNames[i]! == mod then
        for name in env.header.moduleData[i]!.constNames do
          for ax in (← Lean.collectAxioms name) do
            unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
              throwError "unexpected axiom {ax} in {name}"
          count := count + 1
    if count == 0 then throwError "Empty audit: {mod}"
    logInfo m!"Audited {count} owned declarations in {mod}"