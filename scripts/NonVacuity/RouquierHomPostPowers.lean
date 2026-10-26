import OddMath.SKM.RouquierHomPostPowers
import OddMath.SKM.RouquierHomPrincipal
import Lean.Util.CollectAxioms

/-! Consumers at both colour parities, zero and odd content, and zero and
positive natural powers. The Rouquier family remains an input; these checks
are not a construction of a nonzero representation. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierHomPostPowers
private def D (p : ZMod 2) : Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => p
  even_of_odd := fun _ _ _ => even_two

variable {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
  [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
  [∀ a b : B, PiSupercategory ℚ (a ⟶ b)]
  (T : ℤ → B) (muP muM nuM : ℤ)

example : homContentShift (D 1) () (Finsupp.single () 1) = 1 := by
  simp [homContentShift, D]
example : homContentShift (D 0) () (Finsupp.single () 1) = 0 := by
  simp [homContentShift, D]
example (p : ZMod 2) : homContentShift (D p) () 0 = 0 := by simp [homContentShift]

example (W : RouquierFamily (k := ℚ) (B := B) (D 0))
    (h : muM + (D 0).α () = nuM) (Z : homWeightSector T W.obj muP muM) :=
  homContentPostCup_coordinates T W () 0 muP h 0 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 0))
    (h : muM + (D 0).α () = nuM) (Z : homWeightSector T W.obj muP nuM) :=
  homContentPostCap_coordinates T W () 0 muP h 0 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 0))
    (h : muM + (D 0).α () = nuM) (Z : homWeightSector T W.obj muP muM) :=
  homContentPostCup_coordinates T W () 0 muP h 3 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 0))
    (h : muM + (D 0).α () = nuM) (Z : homWeightSector T W.obj muP nuM) :=
  homContentPostCap_coordinates T W () 0 muP h 3 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 0))
    (h : muM + (D 0).α () = nuM) (Z : homWeightSector T W.obj muP muM) :=
  homContentPostCup_coordinates T W () (Finsupp.single () 1) muP h 0 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 0))
    (h : muM + (D 0).α () = nuM) (Z : homWeightSector T W.obj muP nuM) :=
  homContentPostCap_coordinates T W () (Finsupp.single () 1) muP h 0 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 0))
    (h : muM + (D 0).α () = nuM) (Z : homWeightSector T W.obj muP muM) :=
  homContentPostCup_coordinates T W () (Finsupp.single () 1) muP h 3 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 0))
    (h : muM + (D 0).α () = nuM) (Z : homWeightSector T W.obj muP nuM) :=
  homContentPostCap_coordinates T W () (Finsupp.single () 1) muP h 3 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 1))
    (h : muM + (D 1).α () = nuM) (Z : homWeightSector T W.obj muP muM) :=
  homContentPostCup_coordinates T W () 0 muP h 0 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 1))
    (h : muM + (D 1).α () = nuM) (Z : homWeightSector T W.obj muP nuM) :=
  homContentPostCap_coordinates T W () 0 muP h 0 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 1))
    (h : muM + (D 1).α () = nuM) (Z : homWeightSector T W.obj muP muM) :=
  homContentPostCup_coordinates T W () 0 muP h 3 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 1))
    (h : muM + (D 1).α () = nuM) (Z : homWeightSector T W.obj muP nuM) :=
  homContentPostCap_coordinates T W () 0 muP h 3 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 1))
    (h : muM + (D 1).α () = nuM) (Z : homWeightSector T W.obj muP muM) :=
  homContentPostCup_coordinates T W () (Finsupp.single () 1) muP h 0 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 1))
    (h : muM + (D 1).α () = nuM) (Z : homWeightSector T W.obj muP nuM) :=
  homContentPostCap_coordinates T W () (Finsupp.single () 1) muP h 0 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 1))
    (h : muM + (D 1).α () = nuM) (Z : homWeightSector T W.obj muP muM) :=
  homContentPostCup_coordinates T W () (Finsupp.single () 1) muP h 3 Z

example (W : RouquierFamily (k := ℚ) (B := B) (D 1))
    (h : muM + (D 1).α () = nuM) (Z : homWeightSector T W.obj muP nuM) :=
  homContentPostCap_coordinates T W () (Finsupp.single () 1) muP h 3 Z

example (p : ZMod 2) (W : RouquierFamily (k := ℚ) (B := B) (D p))
    (beta : Unit →₀ ℕ) (h : muM + (D p).α () = nuM)
    (n : ℕ) (Z : homWeightSector T W.obj muP muM) :=
  homContentPostDot_power T W () beta muP h n Z

end NonVacuity.RouquierHomPostPowers

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in #[`OddMath.SKM.RouquierHomPostPowers] do
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
#print axioms OddMath.SKM.homContentPostDot_power
#print axioms OddMath.SKM.homContentPostCup_coordinates
#print axioms OddMath.SKM.homContentPostCap_coordinates
