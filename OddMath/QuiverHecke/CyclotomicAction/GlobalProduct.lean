/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeight
import OddMath.QuiverHecke.CyclotomicAction.GlobalSupport
import OddMath.QuiverHecke.CyclotomicAction.Global
import Categorification.TwoRep.BlockSum

/-!
# Products of supercategories for cyclotomic weight spaces

Ports the product-category layer of
`Categorification/KLR/CyclotomicAction/Global.lean`. The product has all
homogeneous components, not just even morphisms. Parity decomposition is
pointwise, with the same two parity indices at every component; no finiteness
of the set of blocks is needed. The construction below does not assert the
uniform nilpotence of a family of dots with unbounded nilpotence exponents.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v w t
variable {k : Type u} [CommRing k] {A : Type t}
  (C : A → Type v) [∀ a, Category.{w} (C a)] [∀ a, Preadditive (C a)]
  [∀ a, Linear k (C a)] [∀ a, Supercategory k (C a)]

/-- A family is homogeneous when all its components have the same parity. -/
def productParity (M N : ∀ a, C a) (p : ZMod 2) : Submodule k (M ⟶ N) where
  carrier := {f | ∀ a, f a ∈ parity (R := k) (M a) (N a) p}
  zero_mem' _ := Submodule.zero_mem _
  add_mem' hf hg a := Submodule.add_mem _ (hf a) (hg a)
  smul_mem' r _ hf a := Submodule.smul_mem _ r (hf a)

/-- Arbitrary products of supercategories have pointwise parity decomposition. -/
instance productSupercategory : Supercategory k (∀ a, C a) where
  parity := productParity C
  isInternal M N := by
    classical
    have hu : (Set.univ : Set (ZMod 2)) = {0, 1} := by ext p; fin_cases p <;> simp
    have hc (a : A) := (isInternal (R := k) (M a) (N a)).isCompl
      (by decide : (0 : ZMod 2) ≠ 1) hu
    apply (DirectSum.isInternal_submodule_iff_isCompl _ (by decide : (0 : ZMod 2) ≠ 1) hu).mpr
    constructor
    · apply Submodule.disjoint_def.mpr
      intro f hf hg
      funext a
      exact Submodule.disjoint_def.mp (hc a).disjoint (f a) (hf a) (hg a)
    · apply Submodule.codisjoint_iff_exists_add_eq.mpr
      intro f
      have hx (a : A) := Submodule.codisjoint_iff_exists_add_eq.mp (hc a).codisjoint (f a)
      choose x hx y hy hxy using hx
      exact ⟨x, hx, y, hy, funext hxy⟩
  id_mem M a := id_mem (M a)
  comp_mem hf hg a := comp_mem (hf a) (hg a)

@[simp] theorem product_mem (M N : ∀ a, C a) (f : M ⟶ N) (p : ZMod 2) :
    f ∈ parity (R := k) M N p ↔ ∀ a, f a ∈ parity (R := k) (M a) (N a) p := Iff.rfl

instance productEval_super (a : A) : IsSuperfunctor k (CategoryTheory.Pi.eval C a) where
  map_mem hf := hf a

/-- Componentwise superfunctors between two products. -/
def productFunctor {B : Type*} (s : B → A) (E : B → Type*) [∀ b, Category (E b)]
    (F : ∀ b, C (s b) ⥤ E b) : (∀ a, C a) ⥤ (∀ b, E b) where
  obj M b := (F b).obj (M (s b))
  map f b := (F b).map (f (s b))
  map_id M := funext fun b => (F b).map_id (M (s b))
  map_comp f g := funext fun b => (F b).map_comp (f (s b)) (g (s b))

section Functor
variable {B : Type*} (s : B → A) (E : B → Type*) [∀ b, Category (E b)]
  [∀ b, Preadditive (E b)] [∀ b, Linear k (E b)] [∀ b, Supercategory k (E b)]
  (F : ∀ b, C (s b) ⥤ E b) [∀ b, (F b).Additive] [∀ b, (F b).Linear k]
  [∀ b, IsSuperfunctor k (F b)]

instance : (productFunctor C s E F).Additive where
  map_add := by intros; exact funext fun b => (F b).map_add

instance : (productFunctor C s E F).Linear k where
  map_smul f r := funext fun b => (F b).map_smul r (f (s b))

instance : IsSuperfunctor k (productFunctor C s E F) where
  map_mem hf b := IsSuperfunctor.map_mem (F := F b) (hf (s b))

end Functor

section Weight
variable {I : Type u} {X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  (Sc : SKM.Scalars D k) [Fintype I] (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (Λ x : X)

/-- The weight space is the product of all content supercategories of this weight,
including the empty content at weight `-Λ`. -/
abbrev globalWeightSpace : SCat.{u, u, u + 1} k :=
  SCat.of k (∀ β : WeightBlocks D Λ x, GlobalContentModules D Sc a ha β.1)

end Weight
end OddMath.QuiverHecke.CyclotomicAction
