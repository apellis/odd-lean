import OddMath.SKM.RouquierDistinctCupInverseChart
import OddMath.SKM.RouquierDistinctLeftCupRotation
import OddMath.SKM.RouquierFTriangle

/-!
# Canonical rotation from the exact raw cup identity

Canonical left units are precisely the inverse-defined raw cups. The
raw cup identity therefore contracts directly against the normalized
canonical counit, with the prescribed inverse right mate retained.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) {Sc : Scalars D k}
  (M : RouquierMulticolour T Sc) {i j : I} (hne : i ≠ j)
  {a b c d : X} (hi : a + D.α i = b) (hj : a + D.α j = c)
  (hij : b + D.α j = d) (hji : c + D.α i = d)

/-- The actual raw cup identity gives invertibility of the canonical
left mate; neither canonical cup is rescaled or replaced. -/
theorem leftCrossMate_isIso_of_raw_cup (u : kˣ)
    (hraw : T.distinctCupLeft hi hj hij hji rfl =
      (u : k) • T.distinctCupRight M hne hi hj hij hji rfl) :
    IsIso (leftCrossMate (T.leftAdjoints.adjL i hi) (T.leftAdjoints.adjL i hji)
      (T.cross j i hi hij hj hji)) := by
  have := M.invNe i j hne hj hji hi hij
  let s := crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij)
  have hs : s ∈ parity (R := k) _ _ (D.parity i * D.parity j) :=
    crossMate_mem (T.adj i hi) (T.adj i hji) _ _ _ (T.cross_mem i j hj hji hi hij)
  have hl : inv s ∈ parity (R := k) _ _ (D.parity i * D.parity j) :=
    inv_mem (asIso s) hs
  apply leftCrossMate_isIso_of_cup_pitchfork
    (T.leftAdjoints.adjL i hi) (T.leftAdjoints.adjL i hji)
    (T.cross j i hi hij hj hji) (inv s) hl u
  rw [T.distinctCupRight_eq_inverseMate M hne hi hj hij hji rfl] at hraw
  exact hraw

end RouquierFamily
end OddMath.SKM
