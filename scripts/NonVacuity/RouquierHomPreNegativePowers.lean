import OddMath.SKM.RouquierHomPreNegativePowers
import OddMath.SKM.RouquierHomPreMateSlide

/-! Odd rank-one checks of the literal pre-mate slide and negative dotted
windows. A supplied family and probe dot unit are construction inputs;
these examples do not construct a nonzero factor representation. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierHomPreNegativePowers

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
  (T : RouquierFamily (k := k) (B := B) oddDatum) (W : ℤ → B) (muM : ℤ)

private theorem edge : -(0 : ℤ) + oddDatum.α () = -(-2) := rfl
private theorem edge₂ : -(2 : ℤ) + oddDatum.α () = -(0 : ℤ) := rfl

/-- At odd parity the literal mate slide has a plus between its two terms. -/
example :
    rouquierMate (homContentSuperAdjunction T W () muM edge)
        (homContentSuperAdjunction T W () muM edge₂) (homContentCrossing T W () muM edge edge₂) ≫
        homContentPreSuperDot T W () muM edge₂ ▷ homContentSuperF T W () muM edge₂ +
      (homContentSuperF T W () muM edge ◁ homContentPreSuperDot T W () muM edge ≫
        rouquierMate (homContentSuperAdjunction T W () muM edge)
          (homContentSuperAdjunction T W () muM edge₂) (homContentCrossing T W () muM edge edge₂)) =
      (homContentSuperAdjunction T W () muM edge).counit ≫
        (homContentSuperAdjunction T W () muM edge₂).unit := by
  simpa [oddDatum] using homContentPreMate_slide T W () muM edge edge₂

example := homContentCrossing_slide T W () muM edge edge₂

variable [IsIso (T.dot () edge)]

example (Z : homWeightSector T.obj W (-2) muM) :
    homReservoirDot T W () muM edge Z ≫ homPreDotInverse T W () muM edge Z = 𝟙 _ :=
  homPreDot_dotInverse T W () muM edge Z

example (Z : homWeightSector T.obj W (-2) muM) :
    homPreDotInverse T W () muM edge Z ≫ homReservoirDot T W () muM edge Z = 𝟙 _ :=
  homPreDotInverse_dot T W () muM edge Z

/-- Exponent -1 is odd and anticommutes with odd Hom morphisms. -/
example {Z Z' : homWeightSector T.obj W (-2) muM} (g : Z ⟶ Z')
    (hg : g ∈ parity (R := k) _ _ 1) :
    g ≫ homPreNegativeCup T W () muM edge 1 Z' =
      -(homPreNegativeCup T W () muM edge 1 Z ≫
        (homContentPreE T W () muM edge ⋙ homContentPreF T W () muM edge).map g) := by
  simpa [oddDatum, sign, neg_one_smul] using
    (homPreNegativeCup_supernatural T W () muM edge 1).naturality hg

example {Z Z' : homWeightSector T.obj W 0 muM} (g : Z ⟶ Z')
    (hg : g ∈ parity (R := k) _ _ 1) :
    (homContentPreF T W () muM edge ⋙ homContentPreE T W () muM edge).map g ≫
        homPreNegativeCap T W () muM edge 1 Z' =
      -(homPreNegativeCap T W () muM edge 1 Z ≫ g) := by
  simpa [oddDatum, sign, neg_one_smul] using
    (homPreNegativeCap_supernatural T W () muM edge 1).naturality hg

/-- Exponent -2 is even, including against odd Hom morphisms. -/
example {Z Z' : homWeightSector T.obj W (-2) muM} (g : Z ⟶ Z')
    (hg : g ∈ parity (R := k) _ _ 1) :
    g ≫ homPreNegativeCup T W () muM edge 2 Z' =
      homPreNegativeCup T W () muM edge 2 Z ≫
        (homContentPreE T W () muM edge ⋙ homContentPreF T W () muM edge).map g := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  simpa [oddDatum, sign, htwo] using
    (homPreNegativeCup_supernatural T W () muM edge 2).naturality hg

example (n : ℕ) (Z : homWeightSector T.obj W (-2) muM) :=
  homPreNegativeCup_coordinates T W () muM edge n Z
example (n : ℕ) (Z : homWeightSector T.obj W 0 muM) :=
  homPreNegativeCap_coordinates T W () muM edge n Z
example (Z : homWeightSector T.obj W (-2) muM) :=
  homPreNegativeCup_zero T W () muM edge Z
example (Z : homWeightSector T.obj W 0 muM) :=
  homPreNegativeCap_zero T W () muM edge Z

/-- The odd negative-power alpha coefficient is nontrivial at this height. -/
example : koszulSign (leftAdjParity oddDatum () 0) ((1 : ZMod 2) * oddDatum.parity ()) = -1 := by
  decide
example : koszulSign (leftAdjParity oddDatum () 0) (1 + (2 : ZMod 2) * oddDatum.parity ()) = -1 := by
  decide

#print axioms homContentCrossing_slide
#print axioms homContentPreMate_slide
#print axioms homPreDot_dotInverse
#print axioms homPreDotInverse_dot
#print axioms homPreDotInverse_power_supernatural
#print axioms homPreNegativeCup_supernatural
#print axioms homPreNegativeCap_supernatural
#print axioms homPreNegativeCup_coordinates
#print axioms homPreNegativeCap_coordinates
#print axioms homPreNegativeCup_zero
#print axioms homPreNegativeCap_zero
end NonVacuity.RouquierHomPreNegativePowers
