/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExistence
import OddMath.QuiverHecke.CyclotomicAction.GlobalProduct

/-! # Separated denominator units on arbitrary products of content categories

The full-ELV factor weight category is the actual product of its content
module categories. Its denominator inverses are assembled componentwise.
A nilpotence exponent may depend on the content component; no exponent on
the entire weight fibre is assumed or inferred.
-/
noncomputable section
open CategoryTheory
namespace OddMath.QuiverHecke.SwappedAssembly
universe u v w
variable {A : Type u} (C : A → Type v) [∀ a, Category.{w} (C a)]
  [∀ a, Preadditive (C a)]

/-- Actual endomorphisms of a product object are units when every component is. -/
theorem productEnd_isUnit (M : ∀ a, C a) (f : End M)
    (hf : ∀ a, IsUnit (f a)) : IsUnit f := by
  classical
  let us : ∀ a, (End (M a))ˣ := fun a => (hf a).unit
  refine ⟨{ val := f, inv := fun a => (↑((us a)⁻¹) : End (M a)),
    val_inv := ?_, inv_val := ?_ }, rfl⟩
  · funext a
    change f a * (↑((us a)⁻¹) : End (M a)) = 1
    have hu : ((us a : (End (M a))ˣ) : End (M a)) = f a := (hf a).unit_spec
    rw [← hu]
    exact (us a).val_inv
  · funext a
    change (↑((us a)⁻¹) : End (M a)) * f a = 1
    have hu : ((us a : (End (M a))ˣ) : End (M a)) = f a := (hf a).unit_spec
    rw [← hu]
    exact (us a).inv_val

/-- The even denominator is a unit using only componentwise nilpotence. -/
theorem product_difference_isUnit (M : ∀ a, C a) (x y : End M)
    (hx : ∀ a, IsUnit (x a)) (hy : ∀ a, IsNilpotent (y a))
    (hcomm : ∀ a, Commute (y a) (x a)) : IsUnit (y - x) := by
  apply productEnd_isUnit C M
  intro a
  change IsUnit (y a - x a)
  simpa only [sub_eq_add_neg, add_comm] using
    (hy a).isUnit_add_left_of_commute (hx a).neg (hcomm a).neg_right

/-- The odd denominator is a unit with no global nilpotence requirement. -/
theorem product_square_difference_isUnit (M : ∀ a, C a) (x y : End M)
    (hx : ∀ a, IsUnit (x a)) (hy : ∀ a, IsNilpotent (y a))
    (hanti : ∀ a, y a * x a = -(x a * y a)) : IsUnit (x ^ 2 - y ^ 2) := by
  apply productEnd_isUnit C M
  intro a
  change IsUnit (x a ^ 2 - y a ^ 2)
  have hc := ProbeReservoir.commute_sq_of_anticommute (hanti a)
  have hu := ((hy a).pow_of_pos two_ne_zero).neg.isUnit_add_left_of_commute
    ((hx a).pow 2)
    (by simpa [pow_two] using ((hc.2.symm.mul_right hc.2.symm).symm).neg_left)
  simpa only [sub_eq_add_neg, add_comm] using hu

/-- The companion square norm used by the odd mate is also componentwise a unit. -/
theorem product_square_sum_isUnit (M : ∀ a, C a) (x y : End M)
    (hx : ∀ a, IsUnit (x a)) (hy : ∀ a, IsNilpotent (y a))
    (hanti : ∀ a, y a * x a = -(x a * y a)) : IsUnit (x ^ 2 + y ^ 2) := by
  apply productEnd_isUnit C M
  intro a
  change IsUnit (x a ^ 2 + y a ^ 2)
  have hc := ProbeReservoir.commute_sq_of_anticommute (hanti a)
  have hu := ((hy a).pow_of_pos two_ne_zero).isUnit_add_left_of_commute
    ((hx a).pow 2)
    (by simpa [pow_two] using ((hc.2.symm.mul_right hc.2.symm).symm))
  simpa only [add_comm] using hu

/-- An even supernatural endomorphism is invertible when its even component
is invertible at every object. The inverse is natural and even; no common
polynomial expression or nilpotence exponent is required. -/
theorem superfunctorEnd_isUnit
    {R : Type*} [CommRing R]
    {B : Type*} [Category B] [Preadditive B] [Linear R B]
    [StringDiagrams.Supercategory R B]
    {E : Type*} [Category E] [Preadditive E] [Linear R E]
    [StringDiagrams.Supercategory R E]
    (F : StringDiagrams.Supercategory.Superfunctor R B E) (x : End F)
    (heven : x ∈ StringDiagrams.Supercategory.parity (R := R) F F 0)
    (hunit : ∀ M, IsUnit (x.app 0 M)) : IsUnit x := by
  classical
  letI : ∀ M, IsIso (x.app 0 M) := fun M => (isUnit_iff_isIso _).1 (hunit M)
  let e : F.toFunctor ≅ F.toFunctor :=
    NatIso.ofComponents (fun M => asIso (x.app 0 M))
      (by intro M N f; exact x.toNatTrans.naturality f)
  let b : End F := StringDiagrams.Supercategory.SuperNatTrans.ofNatTrans e.inv
    (fun M => by
      change (asIso (x.app 0 M)).inv ∈
        StringDiagrams.Supercategory.parity (R := R) _ _ 0
      exact StringDiagrams.Supercategory.inv_mem
        (asIso (x.app 0 M)) (x.app_mem 0 M))
  have hx1 : ∀ M, x.app 1 M = 0 := fun M =>
    StringDiagrams.Supercategory.Superfunctor.app_eq_zero_of_mem heven (by decide) M
  have hxb : x ≫ b = 𝟙 F := by
    apply StringDiagrams.Supercategory.Superfunctor.hom_ext_parity
    · intro M
      change x.app 0 M ≫ e.inv.app M + x.app 1 M ≫ 0 = 𝟙 _
      simpa only [Limits.comp_zero, add_zero] using
        (asIso (x.app 0 M)).hom_inv_id
    · intro M
      change x.app 0 M ≫ 0 + x.app 1 M ≫ e.inv.app M = 0
      simp only [hx1, Limits.comp_zero, Limits.zero_comp, add_zero]
  have hbx : b ≫ x = 𝟙 F := by
    apply StringDiagrams.Supercategory.Superfunctor.hom_ext_parity
    · intro M
      change e.inv.app M ≫ x.app 0 M + 0 ≫ x.app 1 M = 𝟙 _
      simpa only [Limits.zero_comp, add_zero] using
        (asIso (x.app 0 M)).inv_hom_id
    · intro M
      change e.inv.app M ≫ x.app 1 M + 0 ≫ x.app 0 M = 0
      simp only [hx1, Limits.comp_zero, Limits.zero_comp, add_zero]
  exact ⟨⟨x, b, hbx, hxb⟩, rfl⟩

/-- Componentwise units on the actual target product assemble to a unit of
the whole even supernatural endomorphism. Both object and content indices
may be infinite. -/
theorem superfunctorProductEnd_isUnit
    {R : Type*} [CommRing R]
    [∀ a, Linear R (C a)] [∀ a, StringDiagrams.Supercategory R (C a)]
    {B : Type*} [Category B] [Preadditive B] [Linear R B]
    [StringDiagrams.Supercategory R B]
    (F : StringDiagrams.Supercategory.Superfunctor R B (∀ a, C a))
    (x : End F)
    (heven : x ∈ StringDiagrams.Supercategory.parity (R := R) F F 0)
    (hunit : ∀ M a, IsUnit (x.app 0 M a)) : IsUnit x :=
  superfunctorEnd_isUnit F x heven
    (fun M => productEnd_isUnit C (F.obj M) (x.app 0 M) (hunit M))

end OddMath.QuiverHecke.SwappedAssembly
