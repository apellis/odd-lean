/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalProduct
import OddMath.SKM.RouquierData

/-! # Augmented inverse assembly over a weight fibre

BE (1.13)–(1.14): assemble pointwise augmented inverses in arbitrary
products of supercategories. The finite inverse window is common to all
components; the standing cutoff/highest-weight count identity supplies
that window on an original-weight fibre. No finite set of blocks or
injective root map is required.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.SKM
universe u v w t
variable {k : Type w} [CommRing k] {ι : Type t} {C : ι → Type u}
  [∀ a, Category.{v} (C a)] [∀ a, Preadditive (C a)]
  [∀ a, Linear k (C a)] [∀ a, Supercategory k (C a)]
  {A B Z : ∀ a, C a} {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}

private theorem product_sum_apply {X Y : ∀ a, C a}
    (s : Finset ℕ) (h : ℕ → (X ⟶ Y)) (a : ι) :
    (∑ m ∈ s, h m) a = ∑ m ∈ s, h m a := by
  exact (CategoryTheory.Pi.eval C a).map_sum h s

/-- The given component column inverses assemble on the entire product,
without a finiteness condition on its index type. -/
def SuperSumInvFrom.pi
    {f : ∀ a, B a ⟶ A a} {g : ℕ → ∀ a, Z a ⟶ A a}
    (J : ∀ a, SuperSumInvFrom (k := k) (f a) (fun m => g m a) p q n) :
    SuperSumInvFrom (k := k) (show B ⟶ A from f) (fun m => (show Z ⟶ A from g m)) p q n where
  f' a := (J a).f'
  g' m a := (J a).g' m
  f_mem a := (J a).f_mem
  g_mem m a := (J a).g_mem m
  f'_mem a := (J a).f'_mem
  g'_mem m a := (J a).g'_mem m
  total := by
    funext a
    simpa only [Categorification.TwoRep.pi_add_apply, product_sum_apply, CategoryTheory.Pi.comp_apply, CategoryTheory.Pi.id_apply] using (J a).total
  ff := funext fun a => (J a).ff
  fg m hm := funext fun a => (J a).fg m hm
  gf m hm := funext fun a => (J a).gf m hm
  gg m l hm hl := by
    by_cases hml : m = l
    · rw [ite_eq_left hml]
      funext a
      simpa only [CategoryTheory.Pi.comp_apply, CategoryTheory.Pi.id_apply, ite_eq_left hml] using (J a).gg m l hm hl
    · rw [ite_eq_right hml]
      funext a
      simpa only [CategoryTheory.Pi.comp_apply, Categorification.TwoRep.pi_zero_apply, ite_eq_right hml] using (J a).gg m l hm hl

/-- The given component row inverses assemble on an arbitrary product. -/
def SuperSumInvTo.pi
    {f : ∀ a, A a ⟶ B a} {g : ℕ → ∀ a, A a ⟶ Z a}
    (J : ∀ a, SuperSumInvTo (k := k) (f a) (fun m => g m a) p q n) :
    SuperSumInvTo (k := k) (show A ⟶ B from f) (fun m => (show A ⟶ Z from g m)) p q n where
  f' a := (J a).f'
  g' m a := (J a).g' m
  f_mem a := (J a).f_mem
  g_mem m a := (J a).g_mem m
  f'_mem a := (J a).f'_mem
  g'_mem m a := (J a).g'_mem m
  total := by
    funext a
    simpa only [Categorification.TwoRep.pi_add_apply, product_sum_apply, CategoryTheory.Pi.comp_apply, CategoryTheory.Pi.id_apply] using (J a).total
  ff := funext fun a => (J a).ff
  fg m hm := funext fun a => (J a).fg m hm
  gf m hm := funext fun a => (J a).gf m hm
  gg m l hm hl := by
    by_cases hml : m = l
    · rw [ite_eq_left hml]
      funext a
      simpa only [CategoryTheory.Pi.comp_apply, CategoryTheory.Pi.id_apply, ite_eq_left hml] using (J a).gg m l hm hl
    · rw [ite_eq_right hml]
      funext a
      simpa only [CategoryTheory.Pi.comp_apply, Categorification.TwoRep.pi_zero_apply, ite_eq_right hml] using (J a).gg m l hm hl

end OddMath.SKM
