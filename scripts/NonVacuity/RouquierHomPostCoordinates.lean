import OddMath.SKM.RouquierHomPostCoordinates
import Lean.Util.CollectAxioms

/-! Odd rank-one consumers with odd and zero content shift. The family remains an
input; these checks do not construct a nonzero model or prove the principal mate equality. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierHomPostCoordinates
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
  (T : ℤ → B) (W : RouquierFamily (k := ℚ) (B := B) D)
  (muP muM nuM rhoM : ℤ) (h : muM + D.α () = nuM) (h₂ : nuM + D.α () = rhoM)

example : homContentShift D () (Finsupp.single () 1) = 1 := by
  simp [homContentShift, D]

example : homContentShift D () 0 = 0 := by simp [homContentShift]

theorem oddShiftCrossing (Z : homWeightSector T W.obj muP muM) :
    let F := homPost (k := ℚ) (a := T (-muP)) (W.E () h ≫ W.E () h₂)
    (homParityShift (k := ℚ) 1).map
      ((homParityShift (k := ℚ) 1).obj Z ◁ W.cross () () h h₂ h h₂) ≫
        (homShiftConjugationIso F 1 Z).hom =
      (homShiftConjugationIso F 1 Z).hom ≫ (Z ◁ W.cross () () h h₂ h h₂) := by
  have hs : homContentShift D () (Finsupp.single () 1) = 1 := by simp [homContentShift, D]
  have hc := homContentPostFactorCrossing_shift T W () (Finsupp.single () 1) muP h h₂ Z
  dsimp only at hc
  rw [hs] at hc
  exact hc

theorem zeroShiftCrossing (Z : homWeightSector T W.obj muP muM) :
    let F := homPost (k := ℚ) (a := T (-muP)) (W.E () h ≫ W.E () h₂)
    (homParityShift (k := ℚ) 0).map
      ((homParityShift (k := ℚ) 0).obj Z ◁ W.cross () () h h₂ h h₂) ≫
        (homShiftConjugationIso F 0 Z).hom =
      (homShiftConjugationIso F 0 Z).hom ≫ (Z ◁ W.cross () () h h₂ h h₂) := by
  have hs : homContentShift D () 0 = 0 := by simp [homContentShift]
  have hc := homContentPostFactorCrossing_shift T W () 0 muP h h₂ Z
  dsimp only at hc
  rw [hs] at hc
  exact hc

example (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostAdjunction T W () (Finsupp.single () 1) muP h).counit.app Z =
      (homContentPostSourceIso T W () (Finsupp.single () 1) muP h Z).hom ≫
        (homPostCounit (W.adj () h)).app Z :=
  homContentPostAdjunction_counit_coordinates T W () (Finsupp.single () 1) muP h Z

example (Z : homWeightSector T W.obj muP muM) :
    (homContentPostAdjunction T W () 0 muP h).unit.app Z =
      (homPostUnit (W.adj () h)).app Z ≫ (homContentPostTargetIso T W () 0 muP h Z).inv :=
  homContentPostAdjunction_unit_coordinates T W () 0 muP h Z

/-- The prescribed mate is well typed at odd content, without substituting an output-shift adjoint. -/
def oddContentMate :=
  rouquierMate (homContentPostSuperAdjunction T W () (Finsupp.single () 1) muP h)
    (homContentPostSuperAdjunction T W () (Finsupp.single () 1) muP h₂)
    (homContentPostCrossing T W () (Finsupp.single () 1) muP h h₂)

end NonVacuity.RouquierHomPostCoordinates

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in #[`OddMath.SKM.RouquierHomPostCoordinates] do
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
