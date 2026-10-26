import OddMath.SKM.RouquierNormalizedHomAdjunction
import Lean.Util.CollectAxioms

/-! Odd rank-one, all-height consumers. The family is a premise, not a
constructed nonzero model. Both new modules receive a complete owned-declaration audit. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierNormalizedHomAdjunction
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

example (n : ℤ) : (T.leftAdjScalar () n : ℚ) =
    ((koszulSign ((n + 1 : ℤ) : ZMod 2) ((n + 1 : ℤ) : ZMod 2) *
      (if n < 0 then 1 else -1) : ℤ) : ℚ) := by
  simpa [leftAdjParity, D, Datum.h] using T.leftAdjScalar_coe () n

example : (T.leftAdjScalar () (-1) : ℚ) = 1 := by
  norm_num [T.leftAdjScalar_coe, leftAdjParity, D, Datum.h]

example : (T.leftAdjScalar () 0 : ℚ) = 1 := by
  norm_num [T.leftAdjScalar_coe, leftAdjParity, D, Datum.h]

/-- The specified adjunction exists for every reservoir height and probe sector. -/
def reservoirAdjunction (n muM : ℤ) :
    homContentPreE T W () muM (muP := -(n + 2)) (nuP := -n) (by simp [D, Datum.α]) ⊣
      homContentPreF T W () muM (muP := -(n + 2)) (nuP := -n) (by simp [D, Datum.α]) :=
  homContentPreAdjunction T W T.leftAdjoints () muM (by simp [D, Datum.α])

example (n : ℤ) : (T.leftAdjoints.adjL () (rfl : n + D.α () = _)).unit =
    T.leftCup () rfl := T.leftAdjoints_unit () rfl

example (n : ℤ) : (T.leftAdjoints.adjL () (rfl : n + D.α () = _)).counit =
    (((T.leftAdjScalar () n)⁻¹ : ℚˣ) : ℚ) • T.leftCap () rfl :=
  T.leftAdjoints_counit () rfl

example (muM muP nuP : ℤ) (h : -nuP + D.α () = -muP)
    (Z : homWeightSector T.obj W muP muM) :
    (homContentPreAdjunction T W T.leftAdjoints () muM h).unit.app Z =
      (leftUnitor Z).inv ≫ T.leftCup () h ▷ Z ≫
        (associator (T.F () h) (T.E () h) Z).hom ≫
        ((homParityShiftDatum (k := ℚ) (leftAdjParity D () (-nuP))).iso
          (T.F () h ≫ T.E () h ≫ Z)).inv :=
  homContentPreAdjunction_leftAdjoints_unit_app T W () muM h Z
/-- The signed cap holds at every odd rank-one source height, with the specified shifts. -/
example (muM muP nuP : ℤ) (h : -nuP + D.α () = -muP)
    (Z : homWeightSector T.obj W nuP muM) :
    (homContentPreAdjunction T W T.leftAdjoints () muM h).counit.app Z =
      koszulSign (leftAdjParity D () (-nuP)) (leftAdjParity D () (-nuP)) •
        (T.E () h ◁ ((homParityShiftDatum (k := ℚ) (leftAdjParity D () (-nuP))).iso
          (T.F () h ≫ Z)).hom ≫
          (associator (T.E () h) (T.F () h) Z).inv ≫
          ((((T.leftAdjScalar () (-nuP))⁻¹ : ℚˣ) : ℚ) • T.leftCap () h) ▷ Z ≫
          (leftUnitor Z).hom) :=
  homContentPreAdjunction_leftAdjoints_counit_app T W () muM h Z
example (muM muP nuP : ℤ) (h : -nuP + D.α () = -muP)
    (Z Y : homWeightSector T.obj W muP muM) {q : ZMod 2}
    (g : T.F () h ≫ T.E () h ≫ Z ⟶ Y)
    (hg : g ∈ parity (R := ℚ) _ _ q) :
    (homContentPreAdjunction T W T.leftAdjoints () muM h).unit.app Z ≫
      (homParityShift (k := ℚ) (leftAdjParity D () (-nuP))).map g ≫
      ((homParityShiftDatum (k := ℚ) (leftAdjParity D () (-nuP))).iso Y).hom =
    koszulSign (leftAdjParity D () (-nuP)) q •
      ((leftUnitor Z).inv ≫ T.leftCup () h ▷ Z ≫
        (associator (T.F () h) (T.E () h) Z).hom ≫ g) :=
  homContentPreAdjunction_unit_output_coordinates T W () muM h Z Y g hg
end NonVacuity.RouquierNormalizedHomAdjunction

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in #[`OddMath.SKM.RouquierFTriangle, `OddMath.SKM.RouquierNormalizedHomAdjunction] do
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
