import OddMath.SKM.RouquierShiftedAdjunction
import StringDiagrams.Super.Envelope
import StringDiagrams.Super.Superalgebra

/-!
Consumers for shifted left adjunctions. The parity-shift datum is evaluated on
the integral parity envelope, where its comparison is the odd `ζ`. The Hom-sector
adjunction is a signature check for an arbitrary 2-supercategory; no factor left
adjunction is constructed from Rouquier's local inverses here.
-/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.ShiftedAdjunction

private abbrev C := Envelope ℤ (UnitSupercat ℤ)

/-- On the parity envelope the shift datum of parity one is `ζ`, which is odd. -/
example (X : C) : ((homParityShiftDatum (k := ℤ) (C := C) 1).iso X).hom ∈
    parity (R := ℤ) _ _ 1 :=
  (homParityShiftDatum (k := ℤ) (C := C) 1).hom_mem X

example (X : C) : (ParityShiftDatum.pi (k := ℤ) (C := C)).iso X = PiSupercategory.ζ X := rfl

/-- The leftward parity is constant along an edge, so the cup and cap of one
adjunction have a single parity. -/
example {I W : Type*} [AddCommGroup W] (D : Datum I W) (i : I) (x : W) :
    leftAdjParity D i (x + D.α i) = leftAdjParity D i x :=
  leftAdjParity_edge D i rfl

/-- An odd colour at even `⟨hᵢ, x⟩` has odd leftward cup and cap. -/
example {I W : Type*} [AddCommGroup W] (D : Datum I W) (i : I) (x : W)
    (hi : D.parity i = 1) (hx : D.h i x = 0) : leftAdjParity D i x = 1 := by
  simp [leftAdjParity, hi, hx]

section
variable {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℤ (a ⟶ b)]
  [∀ a b : B, Supercategory ℤ (a ⟶ b)] [TwoSupercategory ℤ B]
  [∀ a b : B, PiSupercategory ℤ (a ⟶ b)]

/-- An odd left adjunction gives the Π-shifted precomposition adjunction. -/
example {a b c : B} {F : b ⟶ a} {E : a ⟶ b} (A : ShiftedSuperAdjunction (k := ℤ) F E 1) :
    homPre (k := ℤ) (c := c) E ⋙ PiSupercategory.pi (R := ℤ) ⊣ homPre (k := ℤ) F :=
  homPreShiftAdjunction A ParityShiftDatum.pi

/-- Its unit is the odd cup followed by the odd inverse comparison. -/
example {a b c : B} {F : b ⟶ a} {E : a ⟶ b} (A : ShiftedSuperAdjunction (k := ℤ) F E 1)
    (X : b ⟶ c) :
    (homPreShiftAdjunction (c := c) A ParityShiftDatum.pi).unit.app X =
      (leftUnitor X).inv ≫ A.unit ▷ X ≫ (associator F E X).hom ≫
        F ◁ (PiSupercategory.ζ (R := ℤ) (E ≫ X)).inv := rfl

/-- An even adjunction gives the unshifted reversal. -/
example {a b c : B} {F : b ⟶ a} {E : a ⟶ b} (A : SuperAdjunction (k := ℤ) F E) :
    homPre (k := ℤ) (c := c) E ⋙ 𝟭 _ ⊣ homPre (k := ℤ) F :=
  homPreShiftAdjunction (ShiftedSuperAdjunction.ofSuperAdjunction A) ParityShiftDatum.id
end

#print axioms homParityShiftDatum
#print axioms ShiftedSuperAdjunction.right_triangle_whiskerRight
#print axioms ShiftedSuperAdjunction.left_triangle_whiskerRight
#print axioms homPreShiftAdjunction
#print axioms homContentPreAdjunction
#print axioms leftAdjParity_edge
end NonVacuity.ShiftedAdjunction
