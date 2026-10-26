import OddMath.SKM.RouquierMateSectors

/-!
Signature and axiom audit for the sector realization of the mate coordinates.
Each factor is a sector of itself, and its dotted sector cups and caps are the
factor's dotted cups and caps; the power lemmas are evaluated for an odd dot.
This is not a constructed reservoir–probe action.
-/
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM

section
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

example {a b : B} {E : a ⟶ b} {F : b ⟶ a} (A : SuperAdjunction (k := k) E F) (x : E ⟶ E)
    (hx : x ∈ parity (R := k) _ _ 1) (n : ℕ) :
    (SourceSector.self A x hx).cap n = F ◁ rouquierPower x n ≫ A.counit := rfl

example {b c : B} {E : b ⟶ c} {F : c ⟶ b} (A : SuperAdjunction (k := k) E F) (x : E ⟶ E)
    (hx : x ∈ parity (R := k) _ _ 1) (n : ℕ) :
    (TargetSector.self A x hx).cup n = A.unit ≫ rouquierPower x n ▷ F := rfl

example {a b c : B} (F : c ⟶ a) {E : a ⟶ b} (x : E ⟶ E) :
    (show End (F ≫ E) from F ◁ x) ^ 2 = F ◁ (x ≫ x) := by
  rw [whiskerLeft_rouquierPower (k := k), rouquierPower_succ, rouquierPower_succ,
    rouquierPower_zero, Category.id_comp]
end

#check @SuperRouquierLoc.MateProjectionFormula.of_sectors
#print axioms SuperRouquierLoc.MateProjectionFormula.of_sectors
#print axioms SourceSector.in_dot
#print axioms TargetSector.dot_out
#print axioms whiskerRight_rouquierPower
