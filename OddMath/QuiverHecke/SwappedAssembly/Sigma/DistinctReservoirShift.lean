import OddMath.QuiverHecke.SwappedAssembly.Generators.Cross
import OddMath.SKM.RouquierHomDistinctPostShift
/-! # Parity removals for the distinct reservoir crossing

Brundan–Ellis (1.11), MixedColourBlockCompletion §2 (3)–(4):
the prescribed even beta/xi comparison agrees with the successive
homogeneous parity removals. These identities compare the pure
reservoir crossing with its factor mate.
-/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly
universe u v w r
section
variable {k : Type r} [CommRing k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [Supercategory k C] [PiSupercategory k C]
theorem parityShiftAdd_remove (p q : ZMod 2) (Z : C) :
    (homParityShiftAdd (k := k) p q).hom.app Z ≫
      ((homParityShiftDatum (k := k) (p + q)).iso Z).hom =
    (homParityShift (k := k) q).map ((homParityShiftDatum (k := k) p).iso Z).hom ≫
      ((homParityShiftDatum (k := k) q).iso Z).hom := by
  rcases (show p = 0 ∨ p = 1 by fin_cases p; exact Or.inl rfl; exact Or.inr rfl) with rfl | rfl <;>
    rcases (show q = 0 ∨ q = 1 by fin_cases q; exact Or.inl rfl; exact Or.inr rfl) with rfl | rfl
  · simp [homParityShiftAdd, homParityShift, homParityShiftDatum, ParityShiftDatum.id]
  · simp [homParityShiftAdd, homParityShift, homParityShiftDatum, ParityShiftDatum.id]
  · simp [homParityShiftAdd, homParityShift, homParityShiftDatum, ParityShiftDatum.id]
  · simpa [homParityShiftAdd, homParityShiftDatum, ParityShiftDatum.id,
      homParityShift, ParityShiftDatum.pi] using PiSupercategory.ξ_hom (R := k) Z
end

section Pair
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]

attribute [local reducible] homPost

theorem postPairIso_remove {x a b c : B} (Ei : b ⟶ c) (Z : x ⟶ a) (Ej : a ⟶ b)
    (p q : ZMod 2) :
    (ProbeReservoir.postPairIso (k := k) Ei Z Ej p q).hom ≫
      ((homParityShiftDatum (k := k) (q + p)).iso ((Z ≫ Ej) ≫ Ei)).hom =
    (homParityShift (k := k) p).map
      (((homParityShiftDatum (k := k) q).iso (Z ≫ Ej)).hom ▷ Ei) ≫
      ((homParityShiftDatum (k := k) p).iso ((Z ≫ Ej) ≫ Ei)).hom := by
  simp only [ProbeReservoir.postPairIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [parityShiftAdd_remove, homParityShiftCommute_inv_app]
  simp only [homPost, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem parityShift_transport_remove {p q : ZMod 2} (h : p = q)
    {C : Type*} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [PiSupercategory k C] (Z : C) :
    eqToHom (congrArg (fun r => (homParityShift (k := k) r).obj Z) h) ≫
      ((homParityShiftDatum (k := k) q).iso Z).hom =
      ((homParityShiftDatum (k := k) p).iso Z).hom := by
  subst h
  simp

/-- The even pair comparison transports a homogeneous factor crossing
by the successive parity removals, with the forced naturality sign. -/
theorem postPairCrossing_eq {a b c d x : B} {E₁ : a ⟶ b} {E₂ : d ⟶ c}
    {E₃ : a ⟶ d} {E₄ : b ⟶ c} {r : ZMod 2} (p q : ZMod 2)
    (t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄) (ht : t ∈ parity (R := k) _ _ r) (Z : x ⟶ a) :
    (ProbeReservoir.postPairIso (k := k) E₂ Z E₃ p q).hom ≫
      (homParityShift (k := k) (q + p)).map
        ((associator Z E₃ E₂).hom ≫ Z ◁ t ≫ (associator Z E₁ E₄).inv) ≫
      eqToHom (by rw [add_comm]) ≫
      (ProbeReservoir.postPairIso (k := k) E₄ Z E₁ q p).inv =
    sign k ((q + p) * r) • homShiftedPostCrossing p q t Z := by
  let f := (associator Z E₃ E₂).hom ≫ Z ◁ t ≫ (associator Z E₁ E₄).inv
  have hf : f ∈ parity (R := k) _ _ r := by
    simpa only [zero_add, add_zero, Category.assoc, f] using comp_mem
      (comp_mem (TwoSupercategory.associator_hom_mem (R := k) Z E₃ E₂)
        (TwoSupercategory.whiskerLeft_mem Z ht))
      (inv_mem (associator Z E₁ E₄) (TwoSupercategory.associator_hom_mem (R := k) Z E₁ E₄))
  have hn := (homParityShiftDatum (k := k) (q + p)).hom_naturality hf
  apply (cancel_mono ((ProbeReservoir.postPairIso (k := k) E₄ Z E₁ q p).hom ≫
    ((homParityShiftDatum (k := k) (p + q)).iso ((Z ≫ E₁) ≫ E₄)).hom)).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Linear.smul_comp]
  rw [parityShift_transport_remove (k := k) (add_comm q p), hn]
  simp only [Linear.comp_smul, ← Category.assoc, postPairIso_remove]
  unfold homShiftedPostCrossing
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← TwoSupercategory.comp_whiskerRight (R := k),
    Iso.inv_hom_id, TwoSupercategory.id_whiskerRight (R := k), CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id]
  simp only [Category.comp_id, f]

end Pair
end OddMath.QuiverHecke.SwappedAssembly
