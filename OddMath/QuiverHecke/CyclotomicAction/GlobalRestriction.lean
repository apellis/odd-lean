/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalSupport
import OddMath.QuiverHecke.CyclotomicAction.SuperAdjunction

/-!
# Restriction and adjunction on content supercategories

Ports the block restriction and adjunction (`resBlock`, `globalAdj` on one
block) of `Categorification/KLR/CyclotomicAction/Global.lean`. These are the
balanced-tensor functors on full content supercategories, including odd
module morphisms. The restriction corner intertwines the two central content
projectors, so the even unit and counit of `cyclotomicSuperIndResAdjunction`
restrict without modification. Only positive heights are treated here: the
restriction from one strand to the empty word is not constructed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)
  (i : I) (n : ℕ) (β : Multiset I)

/-- On the restriction corner the lower projector equals the upper projector. -/
theorem restrictionCorner_content (x : (restrictionCorner D Sc i a ha n).toSVec) :
    (restrictionCorner D Sc i a ha n).lact
        (cyclotomicContentIdempotent D Sc a n β) x =
      (restrictionCorner D Sc i a ha n).ract
        (cyclotomicContentIdempotent D Sc a (n + 1) (({i} : Multiset I) + β)) x := by
  apply Subtype.ext
  change cyclotomicAppend D Sc i a n (cyclotomicContentIdempotent D Sc a n β) * x.1 =
    x.1 * cyclotomicContentIdempotent D Sc a (n + 1) (({i} : Multiset I) + β)
  have he := cyclotomicContentIdempotent_append D Sc i a n β 1
  rw [mul_one] at he
  rw [← he, mul_assoc, x.2, cyclotomicContentIdempotent_central]

/-- Balanced-tensor restriction removes the selected colour from content. -/
theorem contentSupported_restriction (M : CyclotomicSupermodules D Sc a ha (n + 1))
    (hM : ContentSupported D Sc a ha (n + 1) (({i} : Multiset I) + β) M) :
    ContentSupported D Sc a ha n β ((cyclotomicSuperRestriction D Sc i a ha n).obj M) := by
  intro z
  change (SuperBimodule.tensor (restrictionCorner D Sc i a ha n) M).lact _ z = z
  induction z using SuperBimodule.tensor_induction_on with
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | btmul x m =>
    rw [SuperBimodule.lact_btmul, restrictionCorner_content,
      SuperBimodule.btmul_ract_lact, hM m]

/-- The restriction superfunctor on the two content blocks. -/
def globalBlockRestriction :
    Superfunctor k (CyclotomicContentModules D Sc a ha (n + 1) (({i} : Multiset I) + β))
      (CyclotomicContentModules D Sc a ha n β) :=
  fullLiftSuperfunctor _ _ ⟨cyclotomicSuperRestriction D Sc i a ha n⟩
    (contentSupported_restriction D Sc a ha i n β)

@[simp] theorem globalBlockRestriction_obj
    (M : CyclotomicContentModules D Sc a ha (n + 1) (({i} : Multiset I) + β)) :
    ((globalBlockRestriction D Sc a ha i n β).obj M).obj =
      (cyclotomicSuperRestriction D Sc i a ha n).obj M.obj := rfl

@[simp] theorem globalBlockRestriction_map
    {M N : CyclotomicContentModules D Sc a ha (n + 1) (({i} : Multiset I) + β)} (f : M ⟶ N) :
    ((globalBlockRestriction D Sc a ha i n β).map f).hom =
      (cyclotomicSuperRestriction D Sc i a ha n).map f.hom := rfl

/-- The original even unit, restricted to the source content. -/
def globalBlockUnit : 𝟭 (CyclotomicContentModules D Sc a ha n β) ⟶
    (globalBlockInduction D Sc a ha i n β).toFunctor ⋙
      (globalBlockRestriction D Sc a ha i n β).toFunctor where
  app M := ⟨(cyclotomicSuperUnit D Sc i a ha n).app M.obj⟩
  naturality _ _ f := InducedCategory.hom_ext ((cyclotomicSuperUnit D Sc i a ha n).naturality f.hom)

/-- The original even counit, restricted to the target content. -/
def globalBlockCounit : (globalBlockRestriction D Sc a ha i n β).toFunctor ⋙
    (globalBlockInduction D Sc a ha i n β).toFunctor ⟶
      𝟭 (CyclotomicContentModules D Sc a ha (n + 1) (({i} : Multiset I) + β)) where
  app M := ⟨(cyclotomicSuperCounit D Sc i a ha n).app M.obj⟩
  naturality _ _ f :=
    InducedCategory.hom_ext ((cyclotomicSuperCounit D Sc i a ha n).naturality f.hom)

@[simp] theorem globalBlockUnit_app (M : CyclotomicContentModules D Sc a ha n β) :
    ((globalBlockUnit D Sc a ha i n β).app M).hom =
      (cyclotomicSuperUnit D Sc i a ha n).app M.obj := rfl

@[simp] theorem globalBlockCounit_app
    (M : CyclotomicContentModules D Sc a ha (n + 1) (({i} : Multiset I) + β)) :
    ((globalBlockCounit D Sc a ha i n β).app M).hom =
      (cyclotomicSuperCounit D Sc i a ha n).app M.obj := rfl

/-- The induction–restriction adjunction restricted to full content blocks. -/
def globalBlockAdjunction :
    (globalBlockInduction D Sc a ha i n β).toFunctor ⊣
      (globalBlockRestriction D Sc a ha i n β).toFunctor where
  unit := globalBlockUnit D Sc a ha i n β
  counit := globalBlockCounit D Sc a ha i n β
  left_triangle_components M :=
    InducedCategory.hom_ext (superInduction_triangle D Sc i a ha n M.obj)
  right_triangle_components M :=
    InducedCategory.hom_ext (superRestriction_triangle D Sc i a ha n M.obj)

theorem globalBlockUnit_mem (M : CyclotomicContentModules D Sc a ha n β) :
    (globalBlockUnit D Sc a ha i n β).app M ∈ parity (R := k) _ _ 0 :=
  superUnitComponent_mem D Sc i a ha n M.obj

theorem globalBlockCounit_mem
    (M : CyclotomicContentModules D Sc a ha (n + 1) (({i} : Multiset I) + β)) :
    (globalBlockCounit D Sc a ha i n β).app M ∈ parity (R := k) _ _ 0 :=
  superCounitComponent_mem D Sc i a ha n M.obj

end OddMath.QuiverHecke.CyclotomicAction
