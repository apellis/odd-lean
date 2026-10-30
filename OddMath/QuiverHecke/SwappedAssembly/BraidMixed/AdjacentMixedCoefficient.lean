/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentMixedTransport

/-! # Coefficient transport in the adjacent mixed braid

Supporting the adjacent mixed component of Brundan–Ellis (1.9): the two
unsigned dot slides transport the inverse coefficient and its square.
At odd colour only the target unit denominator, mapped through the spectator
probe, is cancelled; neither a crossing nor the mixed Q polynomial is cancelled.
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
  (hs : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) =
    nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s))))

include hc h

/-- The inverse coefficient passes through the Q-weighted two-crossing map,
using its proven repeated-dot slides, for both parities. -/
theorem adjacentMixedMove_coeff (hij : i ≠ j) :
    c.a i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z)) ≫
      P.adjacentMixedMove i j s hR hs Z =
    P.adjacentMixedMove i j s hR hs Z ≫
      (P.step (true, j) true s trivial).map
        (c.a i (nextSector (true, j) true s) hR Z) := by
  let W := (P.step (true, j) true _ trivial).obj (hs ▸ Z)
  let F := P.step (true, j) true s trivial
  let R := P.adjacentMixedMove i j s hR hs Z
  let x := P.rpPreDot i s hR W
  let y := P.rpPostDot i s hR W
  let x' := P.rpPreDot i (nextSector (true, j) true s) hR Z
  let y' := P.rpPostDot i (nextSector (true, j) true s) hR Z
  let a := c.a i s hR W
  let b := c.a i (nextSector (true, j) true s) hR Z
  have hx : x ≫ R = R ≫ F.map x' := P.adjacentMixedMove_preDot i j s hR hs Z hij
  have hy : y ≫ R = R ≫ F.map y' := P.adjacentMixedMove_postDot i j s hR hs Z
  change a ≫ R = R ≫ F.map b
  by_cases hi : D.parity i = 0
  · have ha : a ≫ (y - x) = 𝟙 _ := (hc.even i hi s hR W).1
    have hb : (y' - x') ≫ b = 𝟙 _ := (hc.even i hi (nextSector (true, j) true s) hR Z).2
    have hd : (y - x) ≫ R = R ≫ F.map (y' - x') := by
      rw [Preadditive.sub_comp, F.map_sub, Preadditive.comp_sub, hx, hy]
    calc
      a ≫ R = a ≫ R ≫ F.map ((y' - x') ≫ b) := by
        rw [hb, F.map_id, Category.comp_id]
      _ = (a ≫ (y - x)) ≫ R ≫ F.map b := by
        rw [F.map_comp, ← Category.assoc R, ← hd]
        simp only [Category.assoc]
      _ = R ≫ F.map b := by rw [ha, Category.id_comp]
  · have hi' : D.parity i = 1 := by
      generalize hp : D.parity i = p at hi ⊢
      fin_cases p
      · exact False.elim (hi rfl)
      · rfl
    have ha : a ≫ (x ≫ x - y ≫ y) = x - y := (hc.odd i hi' s hR W).1
    have hb : b ≫ (x' ≫ x' - y' ≫ y') = x' - y' := (hc.odd i hi' (nextSector (true, j) true s) hR Z).1
    have hd : (x ≫ x - y ≫ y) ≫ R = R ≫ F.map (x' ≫ x' - y' ≫ y') := by
      simp only [Preadditive.sub_comp, Functor.map_sub, Functor.map_comp,
        Preadditive.comp_sub, Category.assoc]
      rw [hx, hy, ← Category.assoc x, ← Category.assoc y, hx, hy]
      simp only [Category.assoc]
    let v := P.crossDenom h i (nextSector (true, j) true s) hR Z
    have hv : (v : End (P.rpObj i i (nextSector (true, j) true s) hR Z)) = x' ≫ x' - y' ≫ y' := by
      simp [v, crossDenom, hi, sub_eq_add_neg, add_comm, pow_two, End.mul_def, x', y']
    have he : (a ≫ R) ≫ F.map (v : End (P.rpObj i i (nextSector (true, j) true s) hR Z)) =
        (R ≫ F.map b) ≫ F.map (v : End (P.rpObj i i (nextSector (true, j) true s) hR Z)) := by
      rw [hv, Category.assoc, ← hd, ← Category.assoc, ha,
        Category.assoc, ← F.map_comp, hb]
      rw [Preadditive.sub_comp, F.map_sub, Preadditive.comp_sub, hx, hy]
    have hinv : (v : End (P.rpObj i i (nextSector (true, j) true s) hR Z)) ≫
        ((v⁻¹ : (End (P.rpObj i i (nextSector (true, j) true s) hR Z))ˣ) : End (P.rpObj i i (nextSector (true, j) true s) hR Z)) = 𝟙 _ := by
      rw [← End.mul_def, Units.inv_mul]
      rfl
    have hcancel := congrArg (fun f => f ≫ F.map
      ((v⁻¹ : (End (P.rpObj i i (nextSector (true, j) true s) hR Z))ˣ) : End (P.rpObj i i (nextSector (true, j) true s) hR Z))) he
    simp only [Category.assoc, ← F.map_comp, hinv, F.map_id] at hcancel
    rw [Category.comp_id, Category.comp_id] at hcancel
    exact hcancel

/-- The squared coefficient passes through the same two-crossing map. -/
theorem adjacentMixedMove_coeff_sq (hij : i ≠ j) :
    (c.a i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z)) ≫
      c.a i s hR ((P.step (true, j) true _ trivial).obj (hs ▸ Z))) ≫
      P.adjacentMixedMove i j s hR hs Z =
    P.adjacentMixedMove i j s hR hs Z ≫
      (P.step (true, j) true s trivial).map
        (c.a i (nextSector (true, j) true s) hR Z ≫
          c.a i (nextSector (true, j) true s) hR Z) := by
  have ht := P.adjacentMixedMove_coeff c hc h i j s hR hs Z hij
  rw [Functor.map_comp, Category.assoc, ht, ← Category.assoc, ht, Category.assoc]

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
