import OddMath.SKM.RouquierHomContent
import StringDiagrams.Super.Envelope
import StringDiagrams.Super.Superalgebra

/-! Both triangles and the odd action of the parity shift are consumed on
the parity envelope of the one-object integral supercategory. -/
noncomputable section
open CategoryTheory StringDiagrams OddMath.SKM

abbrev ParityTest := Envelope ℤ (UnitSupercat ℤ)

example : homParityShift (k := ℤ) (C := ParityTest) 1 ⊣
    homParityShift (k := ℤ) (C := ParityTest) 1 := homParityShiftAdjunction 1

example (X : ParityTest) :
    (PiSupercategory.pi (R := ℤ)).map (PiSupercategory.ζ (R := ℤ) X).hom =
      -(PiSupercategory.ζ (R := ℤ) ((PiSupercategory.pi (R := ℤ)).obj X)).hom :=
  PiSupercategory.pi_map_ζ X

example {I W : Type*} [AddCommGroup W] (D : Datum I W) (i j : I)
    (hi : D.parity i = 1) (hj : D.parity j = 1) (β : I →₀ ℕ) :
    homContentShift D i (β + Finsupp.single j 1) = homContentShift D i β + 1 := by
  simpa [hi, hj] using homContentShift_add_single D i j β

#print axioms homPiAdjunction
#print axioms homContentShift_add_single
#print axioms homContentPostAdjunction
