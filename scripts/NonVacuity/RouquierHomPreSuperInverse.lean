import OddMath.SKM.RouquierHomPreSuperInverse

/-! Odd rank-one consumers for both normalized precomposition supernatural inverses.
The supplied family is input, not a constructed nonzero representation. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierHomPreSuperInverse

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

variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  (T : RouquierFamily (k := k) (B := B) oddDatum) (W : ℤ → B)
  (muM : ℤ)

private def negative := homContentPreSuperInvNeg T W () muM
  (muP := -4) (nuP := -2) (rhoP := 0) (by rfl) (by rfl) (by decide)

private def positive := homContentPreSuperInvPos T W () muM
  (muP := 0) (nuP := 2) (rhoP := 4) (by rfl) (by rfl) (by decide)

example : True := by have := (negative T W muM).total; trivial
example : True := by have := (negative T W muM).ff; trivial
example : True := by have := (negative T W muM).fg 1 (by decide); trivial
example : True := by have := (negative T W muM).gf 1 (by decide); trivial
example : True := by have := (negative T W muM).gg 0 1 (by decide) (by decide); trivial
example : True := by have := (positive T W muM).total; trivial
example : True := by have := (positive T W muM).ff; trivial
example : True := by have := (positive T W muM).fg 1 (by decide); trivial
example : True := by have := (positive T W muM).gf 1 (by decide); trivial
example : True := by have := (positive T W muM).gg 0 1 (by decide) (by decide); trivial

/-- The negative-height principal inverse anticommutes with odd Hom maps. -/
example {Z Z' : homWeightSector T.obj W (-2) muM} (g : Z ⟶ Z')
    (hg : g ∈ parity (R := k) _ _ 1) :
    (homContentPreE T W () muM (muP := -2) (nuP := 0) (by rfl) ⋙
      homContentPreF T W () muM (muP := -2) (nuP := 0) (by rfl)).map g ≫
      (homContentPreInvNeg T W () muM (muP := -4) (nuP := -2) (rhoP := 0)
        (by rfl) (by rfl) (by decide) Z').f' =
      -((homContentPreInvNeg T W () muM (muP := -4) (nuP := -2) (rhoP := 0)
        (by rfl) (by rfl) (by decide) Z).f' ≫
        (homContentPreF T W () muM (muP := -4) (nuP := -2) (by rfl) ⋙
          homContentPreE T W () muM (muP := -4) (nuP := -2) (by rfl)).map g) := by
  simpa [oddDatum, sign, neg_one_smul] using (homContentPreInvNeg_principal_supernatural T W () muM
    (muP := -4) (nuP := -2) (rhoP := 0) (by rfl) (by rfl) (by decide)).naturality hg

/-- The positive-height principal inverse also anticommutes with odd Hom maps. -/
example {Z Z' : homWeightSector T.obj W 2 muM} (g : Z ⟶ Z')
    (hg : g ∈ parity (R := k) _ _ 1) :
    (homContentPreE T W () muM (muP := 2) (nuP := 4) (by rfl) ⋙
      homContentPreF T W () muM (muP := 2) (nuP := 4) (by rfl)).map g ≫
      (homContentPreInvPos T W () muM (muP := 0) (nuP := 2) (rhoP := 4)
        (by rfl) (by rfl) (by decide) Z').f' =
      -((homContentPreInvPos T W () muM (muP := 0) (nuP := 2) (rhoP := 4)
        (by rfl) (by rfl) (by decide) Z).f' ≫
        (homContentPreF T W () muM (muP := 0) (nuP := 2) (by rfl) ⋙
          homContentPreE T W () muM (muP := 0) (nuP := 2) (by rfl)).map g) := by
  simpa [oddDatum, sign, neg_one_smul] using (homContentPreInvPos_principal_supernatural T W () muM
    (muP := 0) (nuP := 2) (rhoP := 4) (by rfl) (by rfl) (by decide)).naturality hg

/-- The first dotted cup is odd and anticommutes with odd probe maps. -/
example {Z Z' : homWeightSector T.obj W (-2) muM} (g : Z ⟶ Z')
    (hg : g ∈ parity (R := k) _ _ 1) :
    g ≫ homReservoirCup T W () muM
      (muP := -2) (nuP := 0) (by rfl) 1 Z' =
      -(homReservoirCup T W () muM
        (muP := -2) (nuP := 0) (by rfl) 1 Z ≫
        (homContentPreE T W () muM (muP := -2) (nuP := 0) (by rfl) ⋙
          homContentPreF T W () muM (muP := -2) (nuP := 0) (by rfl)).map g) := by
  simpa [oddDatum, sign, neg_one_smul] using
    (homReservoirCup_supernatural T W () muM
      (muP := -2) (nuP := 0) (by rfl) 1).naturality hg

/-- The first dotted cap has the same signed odd naturality. -/
example {Z Z' : homWeightSector T.obj W 2 muM} (g : Z ⟶ Z')
    (hg : g ∈ parity (R := k) _ _ 1) :
    (homContentPreF T W () muM (muP := 0) (nuP := 2) (by rfl) ⋙
      homContentPreE T W () muM (muP := 0) (nuP := 2) (by rfl)).map g ≫
      homReservoirCap T W () muM (muP := 0) (nuP := 2) (by rfl) 1 Z' =
      -(homReservoirCap T W () muM (muP := 0) (nuP := 2) (by rfl) 1 Z ≫ g) := by
  simpa [oddDatum, sign, neg_one_smul] using
    (homReservoirCap_supernatural T W () muM
      (muP := 0) (nuP := 2) (by rfl) 1).naturality hg

example : homPreGamma 1 0 = -1 := by decide
example : homPreBeta 1 (leftAdjParity oddDatum () (-2)) (-2) 1 = -1 := by decide
example : koszulSign (leftAdjParity oddDatum () 2) (1 * oddDatum.parity ()) = -1 := by decide

private def boundaryPos := homContentPreSuperInvPos T W () muM
  (muP := -2) (nuP := 0) (rhoP := 2) (by rfl) (by rfl) (by decide)
private def boundaryNeg := homContentPreSuperInvNeg T W () muM
  (muP := -2) (nuP := 0) (rhoP := 2) (by rfl) (by rfl) (by decide)
example : True := by have := (boundaryPos T W muM).total; trivial
example : True := by have := (boundaryNeg T W muM).total; trivial
example : True := by
  have := homContentPreSuperInv_zero T W () muM
    (muP := -2) (nuP := 0) (rhoP := 2) (by rfl) (by rfl) (by rfl)
  trivial
example (Z : homWeightSector T.obj W 0 muM) :=
  homContentPreInvPos_zero_principal T W () muM
    (muP := -2) (nuP := 0) (rhoP := 2) (by rfl) (by rfl) rfl Z

#print axioms homContentPreSuperInvPos
#print axioms homContentPreSuperInvNeg
#print axioms homContentPreSuperInv_zero
#print axioms homContentPreSuperMate_eq
#print axioms homContentPreInvPos_column_supernatural
#print axioms homContentPreInvNeg_row_supernatural
#print axioms homReservoirCup_supernatural
#print axioms homReservoirCap_supernatural
end NonVacuity.RouquierHomPreSuperInverse
