/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseTransport

/-! # Inverse coefficient along the reverse adjacent move

Only the established coefficient denominator unit is cancelled. Neither
the unequal crossing nor its quadratic polynomial is assumed invertible.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (c : P.CrossCoeff Sc)
  (hc : c.IsInverse) (h : P.CrossCoeffInputs) (i j : I) (s : Sector I)
  (hR : StepValid (true, i) false s)
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

include hc h

/-- The inverse coefficient passes through the unweighted reverse move. -/
theorem adjacentReverseMove_coeff (hij : i ≠ j) :
    (P.step (true, j) true s trivial).map
        (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)) ≫
      P.adjacentReverseMove i j s hR hs Z =
    P.adjacentReverseMove i j s hR hs Z ≫
      c.a i s hR ((P.step (true, j) true _ trivial).obj Z) := by
  let W := (P.step (true, j) true _ trivial).obj Z
  let F := P.step (true, j) true s trivial
  let R := P.adjacentReverseMove i j s hR hs Z
  let x := F.map (P.rpPreDot i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))
  let y := F.map (P.rpPostDot i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))
  let x' := P.rpPreDot i s hR W
  let y' := P.rpPostDot i s hR W
  let a := F.map (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))
  let b := c.a i s hR W
  have hx : x ≫ R = R ≫ x' := P.adjacentReverseMove_preDot i j s hR hs Z hij
  have hy : y ≫ R = R ≫ y' := P.adjacentReverseMove_postDot i j s hR hs Z
  change a ≫ R = R ≫ b
  by_cases hi : D.parity i = 0
  · have ha : a ≫ (y - x) = 𝟙 _ := by
      have he := congrArg F.map
        (hc.even i hi (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).1
      rw [F.map_comp] at he
      erw [F.map_sub, F.map_id] at he
      exact he
    have hb : (y' - x') ≫ b = 𝟙 _ := (hc.even i hi s hR W).2
    have hd : (y - x) ≫ R = R ≫ (y' - x') := by
      rw [Preadditive.sub_comp, Preadditive.comp_sub, hx, hy]
    calc
      a ≫ R = a ≫ R ≫ ((y' - x') ≫ b) := by rw [hb, Category.comp_id]
      _ = (a ≫ (y - x)) ≫ R ≫ b := by
        rw [← Category.assoc R, ← hd]
        simp only [Category.assoc]
      _ = R ≫ b := by rw [ha, Category.id_comp]
  · have hi' : D.parity i = 1 := by
      generalize hp : D.parity i = p at hi ⊢
      fin_cases p
      · exact False.elim (hi rfl)
      · rfl
    have ha : a ≫ (x ≫ x - y ≫ y) = x - y := by
      have he := congrArg F.map
        (hc.odd i hi' (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).1
      rw [F.map_comp] at he
      erw [F.map_sub, F.map_comp, F.map_comp, F.map_sub] at he
      exact he
    have hb : b ≫ (x' ≫ x' - y' ≫ y') = x' - y' := (hc.odd i hi' s hR W).1
    have hd : (x ≫ x - y ≫ y) ≫ R = R ≫ (x' ≫ x' - y' ≫ y') := by
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc]
      rw [hx, hy, ← Category.assoc x, ← Category.assoc y, hx, hy]
      simp only [Category.assoc]
    let v := P.crossDenom h i s hR W
    have hv : (v : End (P.rpObj i i s hR W)) = x' ≫ x' - y' ≫ y' := by
      simp [v, crossDenom, hi, sub_eq_add_neg, add_comm, pow_two, End.mul_def, x', y']
    have he : (a ≫ R) ≫ (v : End (P.rpObj i i s hR W)) =
        (R ≫ b) ≫ (v : End (P.rpObj i i s hR W)) := by
      rw [hv, Category.assoc, ← hd, ← Category.assoc, ha, Category.assoc, hb]
      rw [Preadditive.sub_comp, Preadditive.comp_sub, hx, hy]
    have hinv : (v : End (P.rpObj i i s hR W)) ≫
        ((v⁻¹ : (End (P.rpObj i i s hR W))ˣ) : End (P.rpObj i i s hR W)) = 𝟙 _ := by
      rw [← End.mul_def, Units.inv_mul]
      rfl
    have he' := congrArg (fun f => f ≫
      ((v⁻¹ : (End (P.rpObj i i s hR W))ˣ) : End (P.rpObj i i s hR W))) he
    simp only [Category.assoc, hinv, Category.comp_id] at he'
    erw [Category.comp_id] at he'
    exact he'

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
