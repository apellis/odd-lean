import OddMath.SKM.RouquierLeftCupCap

/-!
Consumers for the leftward cups and caps of super Rouquier data. The parity of
the leftward cup and cap is evaluated at an odd colour, and the conditional
left adjunctions are fed into the Hom-sector precomposition adjunction. The
zigzag obligation itself is not discharged here.
-/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM

section
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}

/-- At an odd colour and even `⟨hᵢ, x⟩` the leftward cup is odd. -/
example (T : RouquierFamily (k := k) (B := B) D) (i : I) {x y : X} (h : x + D.α i = y)
    (hi : D.parity i = 1) (hx : D.h i x = 0) :
    T.leftCup i h ∈ parity (R := k) _ _ 1 := by
  have := T.leftCup_mem i h
  simpa [leftAdjParity, hi, hx] using this

/-- The zigzag obligation gives the content-shifted Hom adjunction. -/
example [∀ a b : B, PiSupercategory k (a ⟶ b)] (T : RouquierFamily (k := k) (B := B) D)
    (H : T.LeftZigzags) (W : X → B) (i : I) (muM : X) {muP nuP : X}
    (h : -nuP + D.α i = -muP) :
    homContentPreE T W i muM h ⊣ homContentPreF T W i muM h :=
  homContentPreAdjunction T W (T.leftAdjointsOfZigzags H) i muM h

/-- The unit of the conditional adjunction is the leftward cup. -/
example (T : RouquierFamily (k := k) (B := B) D) (H : T.LeftZigzags) (i : I) {x y : X}
    (h : x + D.α i = y) : ((T.leftAdjointsOfZigzags H).adjL i h).unit = T.leftCup i h := rfl
end

#print axioms SuperRouquierLoc.cupL_mem
#print axioms SuperRouquierLoc.capL_mem
#print axioms RouquierFamily.leftAdjointsOfZigzags
