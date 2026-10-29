/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Cross
import OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExistence

/-! # Supernaturality of the same-colour crossing coefficient

The coefficient `a` of the mixed block of the same-colour crossing in the swapped action
(`docs/Nondegeneracy/SwappedActionAssembly.md` §2, (A6)) is characterized by
`CrossCoeff.IsInverse`: `a = (y - x)⁻¹` at even colours, and `a (x² - y²) = x - y = (x² - y²) a`
at odd colours, where `x` is the probe dot of the inner letter and `y` the reservoir dot of the
outer letter on the path `(R,P)` of `Eᵢ Eᵢ`.

Both dots are supernatural of parity `pᵢ` (whiskerings of `dotDiag_supernatural`). At even
colours `a` is the inverse of the even supernatural family `y - x`, hence supernatural of parity
`0`. At odd colours the identities alone do not determine `a`: they only fix `a` on the image of
`x² - y²`. Under `CrossCoeffInputs` (F2: `x` is a unit, F3: `y` is nilpotent) the even family
`x² - y²` is invertible, so `a = (x - y) (x² - y²)⁻¹` is supernatural of parity `pᵢ`.

## Main results

* `ProbeReservoir.rpPreDot_supernatural`, `ProbeReservoir.rpPostDot_supernatural`.
* `ProbeReservoir.CrossCoeff.isSupernatural_of_isInverse`: a coefficient satisfying its
  characterizing identities is supernatural, under `CrossCoeffInputs`.
* `ProbeReservoir.crossCoeffOfInputs_isSupernatural`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct

universe u

section Generic

variable {R : Type*} [CommRing R]
  {C : Type*} [Category C] [Preadditive C] [Linear R C] [Supercategory R C]
  {D : Type*} [Category D] [Preadditive D] [Linear R D] [Supercategory R D]

theorem IsSupernatural.sub {p : ZMod 2} {F G : C ⥤ D} {x y : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R p x) (hy : IsSupernatural R p y) :
    IsSupernatural R p fun X => x X - y X := by
  simpa only [sub_eq_add_neg] using IsSupernatural.add hx (IsSupernatural.neg hy)

end Generic

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- The probe dot on the inner letter of the path `(R,P)` is supernatural of parity `pᵢ`. -/
theorem rpPreDot_supernatural (i : I) (t : Sector I) (hv : StepValid (true, i) false t) :
    Supercategory.IsSupernatural k (D.parity i)
      (F := P.step (true, i) true (nextSector (true, i) false t) trivial ⋙
        P.step (true, i) false t hv)
      (G := P.step (true, i) true (nextSector (true, i) false t) trivial ⋙
        P.step (true, i) false t hv)
      (P.rpPreDot i t hv) :=
  (P.dotDiag_supernatural i true _ trivial).whiskerRight (P.step (true, i) false t hv)

/-- The reservoir dot on the outer letter of the path `(R,P)` is supernatural of parity `pᵢ`. -/
theorem rpPostDot_supernatural (i : I) (t : Sector I) (hv : StepValid (true, i) false t) :
    Supercategory.IsSupernatural k (D.parity i)
      (F := P.step (true, i) true (nextSector (true, i) false t) trivial ⋙
        P.step (true, i) false t hv)
      (G := P.step (true, i) true (nextSector (true, i) false t) trivial ⋙
        P.step (true, i) false t hv)
      (P.rpPostDot i t hv) :=
  (P.dotDiag_supernatural i false t hv).whiskerLeft
    (P.step (true, i) true (nextSector (true, i) false t) trivial)

private theorem parity_add_self (p : ZMod 2) : p + p = 0 := by
  fin_cases p <;> rfl

/-- **The same-colour crossing coefficient is supernatural** of parity `pᵢ`, when it satisfies
its characterizing identities `CrossCoeff.IsInverse` and the denominators are invertible
(`CrossCoeffInputs`: the probe dot is a unit and the reservoir dot is nilpotent). At even
colours the identities alone suffice; at odd colours they do not determine the coefficient
without the invertibility of `x² - y²`. -/
theorem CrossCoeff.isSupernatural_of_isInverse (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) : c.IsSupernatural := by
  intro i t hv
  let Fn := P.step (true, i) true (nextSector (true, i) false t) trivial ⋙
    P.step (true, i) false t hv
  have hx := P.rpPreDot_supernatural i t hv
  have hy := P.rpPostDot_supernatural i t hv
  by_cases hi : D.parity i = 0
  · -- `a` is the inverse of the even family `y - x`.
    let e : ∀ Z, Fn.obj Z ≅ Fn.obj Z := fun Z =>
      { hom := P.rpPostDot i t hv Z - P.rpPreDot i t hv Z
        inv := c.a i t hv Z
        hom_inv_id := (hc.even i hi t hv Z).2
        inv_hom_id := (hc.even i hi t hv Z).1 }
    have he : Supercategory.IsSupernatural k 0 (F := Fn) (G := Fn) (fun Z => (e Z).hom) := by
      have := IsSupernatural.sub hy hx
      rw [hi] at this
      exact this
    have := isSupernatural_iso_inv e he
    rw [hi]
    exact this
  · -- `a = (x - y) ≫ (x² - y²)⁻¹`, with `x² - y²` an even unit.
    let d : ∀ Z, (End (P.rpObj i i t hv Z))ˣ := fun Z => P.crossDenom h i t hv Z
    have hd : ∀ Z, ((d Z : (End (P.rpObj i i t hv Z))ˣ) : End (P.rpObj i i t hv Z)) =
        P.rpPreDot i t hv Z ≫ P.rpPreDot i t hv Z -
          P.rpPostDot i t hv Z ≫ P.rpPostDot i t hv Z := fun Z => by
      simp [d, crossDenom, hi, sub_eq_add_neg, add_comm, pow_two, End.mul_def]
    let e : ∀ Z, Fn.obj Z ≅ Fn.obj Z := fun Z =>
      { hom := (d Z : End (P.rpObj i i t hv Z))
        inv := (((d Z)⁻¹ : (End (P.rpObj i i t hv Z))ˣ) : End (P.rpObj i i t hv Z))
        hom_inv_id := by rw [← End.mul_def, Units.inv_mul]; rfl
        inv_hom_id := by rw [← End.mul_def, Units.mul_inv]; rfl }
    have he : Supercategory.IsSupernatural k 0 (F := Fn) (G := Fn) (fun Z => (e Z).hom) := by
      have h2 := IsSupernatural.sub (hx.comp hx) (hy.comp hy)
      rw [parity_add_self] at h2
      convert h2 using 2 with Z
      exact hd Z
    have hinv := isSupernatural_iso_inv e he
    have ha : ∀ Z, c.a i t hv Z =
        (P.rpPreDot i t hv Z - P.rpPostDot i t hv Z) ≫ (e Z).inv := fun Z => by
      have h1 := (hc.odd i (by
        rcases (show D.parity i = 0 ∨ D.parity i = 1 by
          generalize D.parity i = p; fin_cases p <;> simp) with h' | h'
        · exact absurd h' hi
        · exact h') t hv Z).1
      rw [← hd Z] at h1
      rw [← h1, Category.assoc]
      exact ((congrArg (c.a i t hv Z ≫ ·) (e Z).hom_inv_id).trans (Category.comp_id _)).symm
    have hfin := (IsSupernatural.sub hx hy).comp hinv
    rw [add_zero] at hfin
    convert hfin using 2 with Z
    exact ha Z

/-- The coefficient built from `CrossCoeffInputs` is supernatural. -/
theorem crossCoeffOfInputs_isSupernatural (h : P.CrossCoeffInputs) :
    (P.crossCoeffOfInputs h).IsSupernatural :=
  CrossCoeff.isSupernatural_of_isInverse P _ (P.crossCoeffOfInputs_isInverse h) h

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
