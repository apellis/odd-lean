/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.CrossCoeff
import OddMath.QuiverHecke.SwappedAssembly.QuadNe

/-! # Signed transport of the mixed crossing coefficient

Supporting the repeated-outer correction in Brundan–Ellis (1.9). A single
edge with signed dot slides transports the prescribed inverse coefficient
with the same sign. Only the existing coefficient denominator is cancelled;
there is no invertibility assumption on the edge or on Q.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory

section Algebra
variable {k : Type*} [CommRing k]
  {C : Type*} [Category C] [Preadditive C] [Linear k C]
  {A B : C} (x y a : End A) (x' y' b : End B) (f : A ⟶ B) (ε : k)
  (hε : ε * ε = 1)
  (hx : x ≫ f = ε • (f ≫ x')) (hy : y ≫ f = ε • (f ≫ y'))

include hε hx hy

/-- Signed dot transport carries the even inverse difference. -/
theorem signed_inverse_difference_transport
    (ha : a ≫ (y - x) = 𝟙 A) (hb : (y' - x') ≫ b = 𝟙 B) :
    a ≫ f = ε • (f ≫ b) := by
  have hd : (y - x) ≫ f = ε • (f ≫ (y' - x')) := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub, hx, hy, smul_sub]
  have he : f = ε • (a ≫ f ≫ (y' - x')) := by
    calc
      f = (a ≫ (y - x)) ≫ f := by rw [ha, Category.id_comp]
      _ = ε • (a ≫ f ≫ (y' - x')) := by
        rw [Category.assoc, hd, Linear.comp_smul]
  have he' := congrArg (fun g => ε • (g ≫ b)) he
  simpa only [Linear.smul_comp, smul_smul, hε, one_smul,
    Category.assoc, hb, Category.comp_id] using he'.symm

/-- Squared dots have unsigned transport even when each dot has a sign. -/
theorem signed_square_difference_transport :
    (x ≫ x - y ≫ y) ≫ f = f ≫ (x' ≫ x' - y' ≫ y') := by
  have sq (z : End A) (z' : End B) (hz : z ≫ f = ε • (f ≫ z')) :
      (z ≫ z) ≫ f = f ≫ (z' ≫ z') := by
    rw [Category.assoc, hz, Linear.comp_smul, ← Category.assoc, hz,
      Linear.smul_comp, smul_smul, hε, one_smul, Category.assoc]
  rw [Preadditive.sub_comp, Preadditive.comp_sub, sq x x' hx, sq y y' hy]

/-- The odd coefficient follows signed dots; cancel only its target denominator. -/
theorem signed_odd_coefficient_transport
    (ha : a ≫ (x ≫ x - y ≫ y) = x - y)
    (hb : b ≫ (x' ≫ x' - y' ≫ y') = x' - y')
    (v : (End B)ˣ) (hv : (v : End B) = x' ≫ x' - y' ≫ y') :
    a ≫ f = ε • (f ≫ b) := by
  have hd := signed_square_difference_transport x y x' y' f ε hε hx hy
  have he : (a ≫ f) ≫ (v : End B) = (ε • (f ≫ b)) ≫ (v : End B) := by
    rw [hv, Category.assoc, ← hd, ← Category.assoc, ha,
      Linear.smul_comp, Category.assoc, hb]
    rw [Preadditive.sub_comp, Preadditive.comp_sub, hx, hy, smul_sub]
  have hinv : (v : End B) ≫ ((v⁻¹ : (End B)ˣ) : End B) = 𝟙 B := by
    rw [← End.mul_def, Units.inv_mul]
    rfl
  have he' := congrArg (fun g => g ≫ ((v⁻¹ : (End B)ˣ) : End B)) he
  simpa only [Category.assoc, hinv, Category.comp_id] using he'
end Algebra

universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

/-- Signed single-edge coefficient transport between any two functor images of
mixed pairs. The hypotheses concern only the two dots, not the coefficient or
any braid. This includes whiskered and conjugated pairs through linear functors. -/
theorem CrossCoeff.signed_transport (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (i : I) (s t : Sector I)
    (hs : StepValid (true, i) false s) (ht : StepValid (true, i) false t)
    (Z : P.H (nextSector (true, i) true (nextSector (true, i) false s)))
    (W : P.H (nextSector (true, i) true (nextSector (true, i) false t)))
    {C : Type*} [Category C] [Preadditive C] [Linear k C]
    (F : P.H s ⥤ C) [F.Additive] [F.Linear k]
    (G : P.H t ⥤ C) [G.Additive] [G.Linear k]
    (f : F.obj (P.rpObj i i s hs Z) ⟶ G.obj (P.rpObj i i t ht W))
    (ε : k) (hε : ε * ε = 1)
    (hx : F.map (P.rpPreDot i s hs Z) ≫ f =
      ε • (f ≫ G.map (P.rpPreDot i t ht W)))
    (hy : F.map (P.rpPostDot i s hs Z) ≫ f =
      ε • (f ≫ G.map (P.rpPostDot i t ht W))) :
    F.map (c.a i s hs Z) ≫ f = ε • (f ≫ G.map (c.a i t ht W)) := by
  by_cases hi : D.parity i = 0
  · apply signed_inverse_difference_transport _ _ _ _ _ _ f ε hε hx hy
    · have he := congrArg F.map (hc.even i hi s hs Z).1
      rw [F.map_comp] at he
      erw [F.map_sub, F.map_id] at he
      exact he
    · have he := congrArg G.map (hc.even i hi t ht W).2
      rw [G.map_comp] at he
      erw [G.map_sub, G.map_id] at he
      exact he
  · have hi' : D.parity i = 1 := (Supercategory.parity_eq_zero_or_one _).resolve_left hi
    refine signed_odd_coefficient_transport _ _ _ _ _ _ f ε hε hx hy ?_ ?_
      (Units.map (functorAlg (k := k) G _).toMonoidHom (P.crossDenom h i t ht W)) ?_
    · have he := congrArg F.map (hc.odd i hi' s hs Z).1
      rw [F.map_comp] at he
      erw [F.map_sub, F.map_comp, F.map_comp, F.map_sub] at he
      exact he
    · have he := congrArg G.map (hc.odd i hi' t ht W).1
      rw [G.map_comp] at he
      erw [G.map_sub, G.map_comp, G.map_comp, G.map_sub] at he
      exact he
    · simp only [Units.coe_map]
      change G.map (P.crossDenom h i t ht W : End (P.rpObj i i t ht W)) = _
      have hd : (P.crossDenom h i t ht W : End (P.rpObj i i t ht W)) =
          P.rpPreDot i t ht W ≫ P.rpPreDot i t ht W -
            P.rpPostDot i t ht W ≫ P.rpPostDot i t ht W := by
        simp [crossDenom, hi, sub_eq_add_neg, add_comm,
        pow_two, End.mul_def]
      rw [hd]
      erw [G.map_sub, G.map_comp, G.map_comp]

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
