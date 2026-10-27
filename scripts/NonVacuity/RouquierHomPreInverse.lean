import OddMath.SKM.RouquierHomPreInverse

/-! The odd rank-one datum at Hom heights -2 and 0. The factor Rouquier
family is supplied input, not a newly constructed nonzero representation. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierHomPreInverse
private def oddDatum : Datum Unit ℤ where
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
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℤ (a ⟶ b)]
  [∀ a b : B, Supercategory ℤ (a ⟶ b)] [TwoSupercategory ℤ B]
  [∀ a b : B, PiSupercategory ℤ (a ⟶ b)]
  (T : RouquierFamily (k := ℤ) (B := B) oddDatum) (W : ℤ → B)
  (muM : ℤ)

private def negative (Z : homWeightSector T.obj W (-2) muM) :=
  homContentPreInvNeg T W () muM
    (muP := -4) (nuP := -2) (rhoP := 0) (by rfl) (by rfl) (by decide) Z

example (Z : homWeightSector T.obj W (-2) muM) := (negative T W muM Z).total
example (Z : homWeightSector T.obj W (-2) muM) := (negative T W muM Z).ff
example (Z : homWeightSector T.obj W (-2) muM) := (negative T W muM Z).fg 1 (by decide)
example (Z : homWeightSector T.obj W (-2) muM) := (negative T W muM Z).gf 1 (by decide)
example (Z : homWeightSector T.obj W (-2) muM) :=
  (negative T W muM Z).gg 0 1 (by decide) (by decide)
example (Z : homWeightSector T.obj W (-2) muM) :=
  (negative T W muM Z).gg 1 1 (by decide) (by decide)
example (Z : homWeightSector T.obj W (-2) muM) :=
  homContentPreInvNeg_row T W () muM
    (muP := -4) (nuP := -2) (rhoP := 0) (by rfl) (by rfl) (by decide) Z 1

private def boundary (Z : homWeightSector T.obj W 0 muM) :=
  homContentPreInvNeg T W () muM
    (muP := -2) (nuP := 0) (rhoP := 2) (by rfl) (by rfl) (by decide) Z

example (Z : homWeightSector T.obj W 0 muM) := (boundary T W muM Z).total
example (Z : homWeightSector T.obj W 0 muM) := (boundary T W muM Z).ff
example (Z : homWeightSector T.obj W 0 muM) :=
  homContentPreInvNeg_zero_principal T W () muM
    (muP := -2) (nuP := 0) (rhoP := 2) (by rfl) (by rfl) rfl Z

example : homPreGamma 1 0 = -1 := by decide
example : koszulSign (leftAdjParity oddDatum () 2) (1 * oddDatum.parity ()) = -1 := by decide

#print axioms homContentPreInvNeg
#print axioms homContentPreInvNeg_principal
#print axioms homContentPreInvNeg_row
#print axioms homContentPreInvNeg_zero_principal
#print axioms homContentPreMate_coordinates
#print axioms homReservoirCup_factor
end NonVacuity.RouquierHomPreInverse
