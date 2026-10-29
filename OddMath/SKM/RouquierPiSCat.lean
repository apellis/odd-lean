/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RouquierMulticolour
import StringDiagrams.Super.TwoSCat

/-!
# Rouquier families on Π-supercategories

A super Rouquier family (`RouquierFamily`) in the 2-supercategory `𝔖ℭ𝔞𝔱` of supercategories
whose weight-space objects carry Π-structures (Brundan–Ellis, *Monoidal supercategories*,
arXiv:1603.05928v3, Definition 1.7) is a super Rouquier family in `Π-𝔖ℭ𝔞𝔱`, with the same
1-morphisms and 2-morphisms (`RouquierFamily.toPiSCat`); the multicolour relations of
Brundan–Ellis, *Super Kac–Moody 2-categories* (arXiv:1701.04133v2), Definition 1.5, transfer
(`RouquierMulticolour.toPiSCat`).

In `Π-𝔖ℭ𝔞𝔱` the morphism supercategories are Π-supercategories
(`PiTwoSupercategory.homPiLeft`), which the swapped Hom construction requires; in `𝔖ℭ𝔞𝔱` they
are not. Nothing is assumed: all data are reused, and only the vertical powers
`rouquierPower`, defined by recursion, are compared (`rouquierPower_piSCat`).
-/

noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.SKM
universe u v₀ u₀
variable {k : Type u} [CommRing k]

/-- Vertical powers in `Π-𝔖ℭ𝔞𝔱` are those in `𝔖ℭ𝔞𝔱`. -/
theorem rouquierPower_piSCat {A C : PiSCat.{u, v₀, u₀} k} {E : A ⟶ C} (x : E ⟶ E) (n : ℕ) :
    rouquierPower (B := PiSCat.{u, v₀, u₀} k) x n =
      rouquierPower (B := SCat.{u, v₀, u₀} k) (a := A.toSCat) (b := C.toSCat) x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change rouquierPower (B := PiSCat.{u, v₀, u₀} k) x n ≫ x = _
    rw [ih]
    rfl

/-- `rouquierPower_piSCat` as an equality of families. -/
theorem rouquierPower_piSCat_eq {A C : PiSCat.{u, v₀, u₀} k} {E : A ⟶ C} (x : E ⟶ E) :
    rouquierPower (B := PiSCat.{u, v₀, u₀} k) x =
      rouquierPower (B := SCat.{u, v₀, u₀} k) (a := A.toSCat) (b := C.toSCat) x :=
  funext (rouquierPower_piSCat x)

variable {I X : Type*} [AddCommGroup X] {D : Datum I X}

/-- A Rouquier family in `𝔖ℭ𝔞𝔱` whose objects carry Π-structures, as a Rouquier family in
`Π-𝔖ℭ𝔞𝔱` with the same generators, adjunctions and local inverses. -/
def RouquierFamily.toPiSCat
    (T : RouquierFamily (k := k) (B := TwoSCat.of k (SCat.{u, v₀, u₀} k)) D)
    (π : ∀ x, PiSupercategory k (show SCat.{u, v₀, u₀} k from T.obj x)) :
    RouquierFamily (k := k) (B := PiSCat.{u, v₀, u₀} k) D where
  obj x := @PiSCat.mk k _ (show SCat.{u, v₀, u₀} k from T.obj x) (π x)
  E := T.E
  dot := T.dot
  dot_mem := T.dot_mem
  cross := T.cross
  cross_mem := T.cross_mem
  F := T.F
  adj i _ _ h :=
    { unit := (T.adj i h).unit
      counit := (T.adj i h).counit
      unit_mem := (T.adj i h).unit_mem
      counit_mem := (T.adj i h).counit_mem
      left_triangle := (T.adj i h).left_triangle
      right_triangle := (T.adj i h).right_triangle }
  square := T.square
  braid := T.braid
  loc i _ _ _ h₁ h₂ :=
    { dot₁_mem := (T.loc i h₁ h₂).dot₁_mem
      dot₂_mem := (T.loc i h₁ h₂).dot₂_mem
      cross_mem := (T.loc i h₁ h₂).cross_mem
      slide_left := (T.loc i h₁ h₂).slide_left
      slide_right := (T.loc i h₁ h₂).slide_right
      invPos := fun hh => by
        rw [rouquierPower_piSCat_eq]
        exact (T.loc i h₁ h₂).invPos hh
      invNeg := fun hh => by
        rw [rouquierPower_piSCat_eq]
        exact (T.loc i h₁ h₂).invNeg hh }

/-- The multicolour relations transfer to `Π-𝔖ℭ𝔞𝔱`. -/
theorem RouquierMulticolour.toPiSCat
    {T : RouquierFamily (k := k) (B := TwoSCat.of k (SCat.{u, v₀, u₀} k)) D}
    (π : ∀ x, PiSupercategory k (show SCat.{u, v₀, u₀} k from T.obj x))
    {Sc : Scalars D k} (h : RouquierMulticolour T Sc) :
    RouquierMulticolour (T.toPiSCat π) Sc where
  quadZero := h.quadZero
  quadNe i j hij hd _ _ _ _ h₁ h₂ h₃ h₄ := by
    simp only [rouquierPower_piSCat]
    exact h.quadNe i j hij hd h₁ h₂ h₃ h₄
  slideLeft := h.slideLeft
  slideRight := h.slideRight
  braid := h.braid
  braidEq i j hij _ _ _ _ _ _ hab haf hbc hbe hfc hcd hed := by
    rw [rouquierPower_piSCat_eq, rouquierPower_piSCat_eq, rouquierPower_piSCat_eq]
    exact h.braidEq i j hij hab haf hbc hbe hfc hcd hed
  invNe := h.invNe

end OddMath.SKM
