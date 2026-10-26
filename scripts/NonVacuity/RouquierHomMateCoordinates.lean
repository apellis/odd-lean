import OddMath.SKM.RouquierHomMateCoordinates
import Lean.Util.CollectAxioms

/-! Odd rank-one consumers at arbitrary weights. The Rouquier family is an input,
not a constructed nonzero model. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierHomMateCoordinates
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

example (muM muP nuP rhoP : ℤ) (h : -nuP + D.α () = -muP)
    (h₂ : -rhoP + D.α () = -nuP)
    (Z : homWeightSector T.obj W nuP muM) :
    let P := homParityShiftDatum (k := ℚ) (leftAdjParity D () (-nuP))
    let P₂ := homParityShiftDatum (k := ℚ) (leftAdjParity D () (-rhoP))
    T.E () h ◁ (P.iso (T.F () h ≫ Z)).inv ≫
      (rouquierMate (homContentSuperAdjunction T W () muM h)
        (homContentSuperAdjunction T W () muM h₂)
        (homContentCrossing T W () muM h h₂)).app (D.parity ()) Z ≫
      (P₂.iso (T.F () h₂ ≫ T.E () h₂ ≫ Z)).hom =
    (leftUnitor (T.E () h ≫ T.F () h ≫ Z)).inv ≫
      T.leftCup () h₂ ▷ (T.E () h ≫ T.F () h ≫ Z) ≫
      (associator (T.F () h₂) (T.E () h₂) (T.E () h ≫ T.F () h ≫ Z)).hom ≫
      T.F () h₂ ◁ ((homContentCrossing T W () muM h h₂).app (D.parity ()) (T.F () h ≫ Z) ≫
        T.E () h₂ ◁ ((associator (T.E () h) (T.F () h) Z).inv ≫
          ((((T.leftAdjScalar () (-nuP))⁻¹ : ℚˣ) : ℚ) • T.leftCap () h) ▷ Z ≫
          (leftUnitor Z).hom)) :=
  homContentCrossing_coordinates_raw T W () muM h h₂ Z

theorem atHeightZero (muM : ℤ) (Z : homWeightSector T.obj W 0 muM) :
    let h : -(0 : ℤ) + D.α () = -(-2 : ℤ) := by rfl
    let h₂ : -(2 : ℤ) + D.α () = -(0 : ℤ) := by rfl
    let P := homParityShiftDatum (k := ℚ) (leftAdjParity D () (-(0 : ℤ)))
    let P₂ := homParityShiftDatum (k := ℚ) (leftAdjParity D () (-(2 : ℤ)))
    T.E () h ◁ (P.iso (T.F () h ≫ Z)).inv ≫
      (rouquierMate (homContentSuperAdjunction T W () muM h)
        (homContentSuperAdjunction T W () muM h₂)
        (homContentCrossing T W () muM h h₂)).app (D.parity ()) Z ≫
      (P₂.iso (T.F () h₂ ≫ T.E () h₂ ≫ Z)).hom =
    (leftUnitor (T.E () h ≫ T.F () h ≫ Z)).inv ≫
      T.leftCup () h₂ ▷ (T.E () h ≫ T.F () h ≫ Z) ≫
      (associator (T.F () h₂) (T.E () h₂) (T.E () h ≫ T.F () h ≫ Z)).hom ≫
      T.F () h₂ ◁ ((homContentCrossing T W () muM h h₂).app (D.parity ()) (T.F () h ≫ Z) ≫
        T.E () h₂ ◁ ((associator (T.E () h) (T.F () h) Z).inv ≫
          ((((T.leftAdjScalar () (-(0 : ℤ)))⁻¹ : ℚˣ) : ℚ) • T.leftCap () h) ▷ Z ≫
          (leftUnitor Z).hom)) := by
  dsimp only
  exact homContentCrossing_coordinates_raw T W () muM (by rfl) (by rfl) Z

end NonVacuity.RouquierHomMateCoordinates

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in #[`OddMath.SKM.RouquierHomMateCoordinates] do
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
