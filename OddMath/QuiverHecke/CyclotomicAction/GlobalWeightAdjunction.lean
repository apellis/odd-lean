/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalHeightAdjunction
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightInduction
import OddMath.QuiverHecke.CyclotomicAction.ActionSupercategory

/-!
# The induction–restriction adjunction on cyclotomic weight spaces

Ports the adjunction `globalE ⊣ globalF` of
`Categorification/KLR/CyclotomicAction/Global.lean`. At a block `blockSucc β`
the unit and counit are those of `globalContentAdjunction`, transported along
`inductionComponent_blockSucc`; at a block with no predecessor the induced
component is a zero supermodule and the counit is zero. All components are
even, and `globalActionAdjunction` packages the result as an
`SKM.SuperAdjunction` in the `SCat` action target of `ActionSupercategory`.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)

/-- A superfunctor equality, read on morphisms through the induced object equalities. -/
theorem superfunctor_map_of_eq {C₁ C₂ : Type*} [Category C₁] [Preadditive C₁] [Linear k C₁]
    [Supercategory k C₁] [Category C₂] [Preadditive C₂] [Linear k C₂] [Supercategory k C₂]
    {G G' : Superfunctor k C₁ C₂} (hG : G = G') {M M' : C₁} (f : M ⟶ M') :
    G.map f = eqToHom (by rw [hG]) ≫ G'.map f ≫ eqToHom (by rw [hG]) := by
  subst hG
  simp

theorem eqToHom_mem_parity_zero {C : Type*} [Category C] [Preadditive C] [Linear k C]
    [Supercategory k C] {M N : C} (e : M = N) : eqToHom e ∈ parity (R := k) M N 0 := by
  subst e
  exact id_mem M

theorem heightContentCastAdjunction_unit_mem {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m')
    (hγ : γ = γ') (M : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m γ)) :
    (heightContentCastAdjunction D Sc a ha hm hγ).unit.app M ∈ parity (R := k) _ _ 0 := by
  subst hm
  subst hγ
  exact id_mem M

theorem heightContentCastAdjunction_counit_mem {m m' : ℕ} {γ γ' : Multiset I} (hm : m = m')
    (hγ : γ = γ') (M : ObjectProperty.FullSubcategory (heightContentSupported D Sc a ha m' γ')) :
    (heightContentCastAdjunction D Sc a ha hm hγ).counit.app M ∈ parity (R := k) _ _ 0 := by
  subst hm
  subst hγ
  exact id_mem M

theorem globalContentAdjunction_unit_mem (i : I) {β δ : Multiset I} (h : {i} + β = δ)
    (M : GlobalContentModules D Sc a ha β) :
    (globalContentAdjunction D Sc i a ha h).unit.app M ∈ parity (R := k) _ _ 0 := by
  rw [globalContentAdjunction, Adjunction.comp_unit_app]
  rw [← zero_add (0 : ZMod 2)]
  exact comp_mem (heightContentUnit_mem D Sc i a ha β.card β rfl M)
    (IsSuperfunctor.map_mem (heightContentCastAdjunction_unit_mem D Sc a ha _ _ _))

theorem globalContentAdjunction_counit_mem (i : I) {β δ : Multiset I} (h : {i} + β = δ)
    (M : GlobalContentModules D Sc a ha δ) :
    (globalContentAdjunction D Sc i a ha h).counit.app M ∈ parity (R := k) _ _ 0 := by
  rw [globalContentAdjunction, Adjunction.comp_counit_app]
  rw [← zero_add (0 : ZMod 2)]
  exact comp_mem (IsSuperfunctor.map_mem (heightContentCounit_mem D Sc i a ha β.card β rfl _))
    (heightContentCastAdjunction_counit_mem D Sc a ha _ _ _)

section Weight
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- Content induction from a block of weight `x` to its successor. -/
abbrev blockInd (β : WeightBlocks D Λ x) :=
  globalContentInduction D Sc i a ha (blockSucc_val D Λ i h β).symm

/-- Content restriction from the successor of a block of weight `x`. -/
abbrev blockRes (β : WeightBlocks D Λ x) :=
  globalContentRestriction D Sc i a ha (blockSucc_val D Λ i h β).symm

/-- The content adjunction between a block and its successor. -/
abbrev blockAdj (β : WeightBlocks D Λ x) :=
  globalContentAdjunction D Sc i a ha (blockSucc_val D Λ i h β).symm

theorem inductionComponent_obj_blockSucc (β : WeightBlocks D Λ x)
    (M : WeightProduct D Sc a ha Λ x) :
    (inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).obj M =
      (blockInd D Sc a ha i Λ h β).obj (M β) := by
  rw [inductionComponent_blockSucc]
  rfl

theorem inductionComponent_map_blockSucc (β : WeightBlocks D Λ x)
    {M M' : WeightProduct D Sc a ha Λ x} (f : M ⟶ M') :
    (inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).map f =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M) ≫
        (blockInd D Sc a ha i Λ h β).map (f β) ≫
          eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M').symm :=
  superfunctor_map_of_eq (inductionComponent_blockSucc D Sc a ha i Λ h β) f

/-- The unit component at a block of weight `x`. -/
def globalWeightUnitApp (β : WeightBlocks D Λ x) (M : WeightProduct D Sc a ha Λ x) :
    M β ⟶ (blockRes D Sc a ha i Λ h β).obj
      ((inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).obj M) :=
  (blockAdj D Sc a ha i Λ h β).unit.app (M β) ≫
    (blockRes D Sc a ha i Λ h β).map
      (eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M).symm)

theorem globalWeightUnitApp_naturality (β : WeightBlocks D Λ x)
    {M M' : WeightProduct D Sc a ha Λ x} (f : M ⟶ M') :
    f β ≫ globalWeightUnitApp D Sc a ha i Λ h β M' =
      globalWeightUnitApp D Sc a ha i Λ h β M ≫ (blockRes D Sc a ha i Λ h β).map
        ((inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [inductionComponent_map_blockSucc]
  simp only [globalWeightUnitApp, Superfunctor.map, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [Functor.map_comp, ← Adjunction.unit_naturality_assoc]

/-- The unit on weight spaces. -/
def globalWeightUnit : 𝟭 (WeightProduct D Sc a ha Λ x) ⟶
    globalEFunctor D Sc a ha i Λ h ⋙ (globalF D Sc i a ha Λ h).toFunctor where
  app M β := globalWeightUnitApp D Sc a ha i Λ h β M
  naturality _ _ f := funext fun β => globalWeightUnitApp_naturality D Sc a ha i Λ h β f

/-- The counit at a block with a chosen predecessor. -/
def globalWeightCounitVia (N : WeightProduct D Sc a ha Λ y) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (inductionComponent D Sc a ha i Λ h δ).obj ((globalF D Sc i a ha Λ h).obj N) ⟶ N δ := by
  subst hβ
  exact eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β _) ≫
    (blockAdj D Sc a ha i Λ h β).counit.app (N (blockSucc D Λ i h β))

theorem globalWeightCounitVia_eq (N : WeightProduct D Sc a ha Λ y) (β β' : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) (hβ' : blockSucc D Λ i h β' = δ) :
    globalWeightCounitVia D Sc a ha i Λ h N β δ hβ =
      globalWeightCounitVia D Sc a ha i Λ h N β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The counit component at a block: through the predecessor, or zero. -/
def globalWeightCounitComponent (N : WeightProduct D Sc a ha Λ y) (δ : WeightBlocks D Λ y) :
    (inductionComponent D Sc a ha i Λ h δ).obj ((globalF D Sc i a ha Λ h).obj N) ⟶ N δ :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    globalWeightCounitVia D Sc a ha i Λ h N hδ.choose δ hδ.choose_spec
  else 0

theorem globalWeightCounitComponent_blockSucc (N : WeightProduct D Sc a ha Λ y)
    (β : WeightBlocks D Λ x) :
    globalWeightCounitComponent D Sc a ha i Λ h N (blockSucc D Λ i h β) =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β
        ((globalF D Sc i a ha Λ h).obj N)) ≫
        (blockAdj D Sc a ha i Λ h β).counit.app (N (blockSucc D Λ i h β)) := by
  unfold globalWeightCounitComponent
  split
  · rename_i hc
    exact globalWeightCounitVia_eq D Sc a ha i Λ h N _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem globalWeightCounitComponent_naturality (β : WeightBlocks D Λ x)
    {N N' : WeightProduct D Sc a ha Λ y} (g : N ⟶ N') :
    (inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).map
        ((globalF D Sc i a ha Λ h).map g) ≫
      globalWeightCounitComponent D Sc a ha i Λ h N' (blockSucc D Λ i h β) =
    globalWeightCounitComponent D Sc a ha i Λ h N (blockSucc D Λ i h β) ≫
      g (blockSucc D Λ i h β) := by
  rw [inductionComponent_map_blockSucc, globalWeightCounitComponent_blockSucc,
    globalWeightCounitComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  congr 1
  exact (blockAdj D Sc a ha i Λ h β).counit_naturality (g (blockSucc D Λ i h β))

/-- The counit on weight spaces. -/
def globalWeightCounit : (globalF D Sc i a ha Λ h).toFunctor ⋙ globalEFunctor D Sc a ha i Λ h ⟶
    𝟭 (WeightProduct D Sc a ha Λ y) where
  app N δ := globalWeightCounitComponent D Sc a ha i Λ h N δ
  naturality N N' g := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact globalWeightCounitComponent_naturality D Sc a ha i Λ h β g
    · exact (inductionComponent_isZero D Sc a ha i Λ h δ hδ _).eq_of_src _ _

theorem globalWeight_left_triangle (β : WeightBlocks D Λ x) (M : WeightProduct D Sc a ha Λ x) :
    (inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).map
        ((globalWeightUnit D Sc a ha i Λ h).app M) ≫
      globalWeightCounitComponent D Sc a ha i Λ h ((globalEFunctor D Sc a ha i Λ h).obj M)
        (blockSucc D Λ i h β) = 𝟙 _ := by
  rw [inductionComponent_map_blockSucc, globalWeightCounitComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  change eqToHom _ ≫ (blockInd D Sc a ha i Λ h β).map (globalWeightUnitApp D Sc a ha i Λ h β M) ≫
    _ = _
  simp only [globalWeightUnitApp, Superfunctor.map, Functor.map_comp, Category.assoc]
  erw [Adjunction.counit_naturality, Adjunction.left_triangle_components_assoc]
  simp

theorem globalWeight_right_triangle (β : WeightBlocks D Λ x) (N : WeightProduct D Sc a ha Λ y) :
    globalWeightUnitApp D Sc a ha i Λ h β ((globalF D Sc i a ha Λ h).obj N) ≫
      (blockRes D Sc a ha i Λ h β).map
        (globalWeightCounitComponent D Sc a ha i Λ h N (blockSucc D Λ i h β)) = 𝟙 _ := by
  rw [globalWeightCounitComponent_blockSucc]
  simp only [globalWeightUnitApp, Superfunctor.map, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact (blockAdj D Sc a ha i Λ h β).right_triangle_components _

/-- **Induction is left adjoint to restriction on weight spaces.** -/
def globalWeightAdjunction :
    globalEFunctor D Sc a ha i Λ h ⊣ (globalF D Sc i a ha Λ h).toFunctor where
  unit := globalWeightUnit D Sc a ha i Λ h
  counit := globalWeightCounit D Sc a ha i Λ h
  left_triangle_components M := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact globalWeight_left_triangle D Sc a ha i Λ h β M
    · exact (inductionComponent_isZero D Sc a ha i Λ h δ hδ _).eq_of_src _ _
  right_triangle_components N := funext fun β => globalWeight_right_triangle D Sc a ha i Λ h β N

theorem globalWeightUnitApp_mem (β : WeightBlocks D Λ x) (M : WeightProduct D Sc a ha Λ x) :
    globalWeightUnitApp D Sc a ha i Λ h β M ∈ parity (R := k) _ _ 0 := by
  unfold globalWeightUnitApp
  rw [← zero_add (0 : ZMod 2)]
  exact comp_mem (globalContentAdjunction_unit_mem D Sc a ha i (blockSucc_val D Λ i h β).symm (M β))
    (IsSuperfunctor.map_mem (F := (blockRes D Sc a ha i Λ h β).toFunctor)
      (eqToHom_mem_parity_zero (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M).symm))

theorem globalWeightUnit_mem (M : WeightProduct D Sc a ha Λ x) :
    (globalWeightUnit D Sc a ha i Λ h).app M ∈ parity (R := k) _ _ 0 := fun β =>
  globalWeightUnitApp_mem D Sc a ha i Λ h β M

theorem globalWeightCounit_mem (N : WeightProduct D Sc a ha Λ y) :
    (globalWeightCounit D Sc a ha i Λ h).app N ∈ parity (R := k) _ _ 0 := fun δ => by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change globalWeightCounitComponent D Sc a ha i Λ h N (blockSucc D Λ i h β) ∈ _
    rw [globalWeightCounitComponent_blockSucc, ← zero_add (0 : ZMod 2)]
    exact comp_mem (eqToHom_mem_parity_zero (inductionComponent_obj_blockSucc D Sc a ha i Λ h β
        ((globalF D Sc i a ha Λ h).obj N)))
      (globalContentAdjunction_counit_mem D Sc a ha i (blockSucc_val D Λ i h β).symm
        (N (blockSucc D Λ i h β)))
  · rw [(inductionComponent_isZero D Sc a ha i Λ h δ hδ _).eq_of_src
      ((globalWeightCounit D Sc a ha i Λ h).app N δ) 0]
    exact Submodule.zero_mem _

/-- Weight-space induction as a 1-morphism of the action target. -/
def globalActionE : (globalWeightSpace D Sc a ha Λ x : cyclotomicActionTarget (k := k)) ⟶
    (globalWeightSpace D Sc a ha Λ y : cyclotomicActionTarget (k := k)) :=
  globalE D Sc a ha i Λ h

/-- Weight-space restriction as a 1-morphism of the action target. -/
def globalActionF : (globalWeightSpace D Sc a ha Λ y : cyclotomicActionTarget (k := k)) ⟶
    (globalWeightSpace D Sc a ha Λ x : cyclotomicActionTarget (k := k)) :=
  globalF D Sc i a ha Λ h

/-- The weight-space unit as an even supernatural transformation. -/
def globalActionUnit : 𝟙 _ ⟶ globalActionE D Sc a ha i Λ h ≫ globalActionF D Sc a ha i Λ h :=
  SuperNatTrans.ofNatTrans (globalWeightUnit D Sc a ha i Λ h)
    (globalWeightUnit_mem D Sc a ha i Λ h)

/-- The weight-space counit as an even supernatural transformation. -/
def globalActionCounit : globalActionF D Sc a ha i Λ h ≫ globalActionE D Sc a ha i Λ h ⟶ 𝟙 _ :=
  SuperNatTrans.ofNatTrans (globalWeightCounit D Sc a ha i Λ h)
    (globalWeightCounit_mem D Sc a ha i Λ h)

/-- **The even adjunction `E_i ⊣ F_i` on weight spaces** in the Rouquier interface. -/
def globalActionAdjunction :
    SKM.SuperAdjunction (k := k) (globalActionE D Sc a ha i Λ h) (globalActionF D Sc a ha i Λ h) where
  unit := globalActionUnit D Sc a ha i Λ h
  counit := globalActionCounit D Sc a ha i Λ h
  unit_mem := Superfunctor.mem_parity_iff_isHomogeneous.2
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)
  counit_mem := Superfunctor.mem_parity_iff_isHomogeneous.2
    (SuperNatTrans.ofNatTrans_isHomogeneous _ _)
  left_triangle := by
    simp only [SCat.leftUnitor_inv, SCat.associator_hom, SCat.rightUnitor_hom]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    apply Superfunctor.hom_ext_parity
    · intro M
      change _ = 𝟙 ((globalEFunctor D Sc a ha i Λ h).obj M)
      simp [globalActionUnit, globalActionCounit, SuperNatTrans.ofNatTrans,
        globalActionE, globalE, Superfunctor.map,
        Superfunctor.obj]
      exact (globalWeightAdjunction D Sc a ha i Λ h).left_triangle_components M
    · intro M
      simp [globalActionUnit, globalActionCounit, SuperNatTrans.ofNatTrans]
  right_triangle := by
    simp only [SCat.rightUnitor_inv, SCat.associator_inv, SCat.leftUnitor_hom]
    erw [Category.id_comp, Category.id_comp, Category.comp_id]
    apply Superfunctor.hom_ext_parity
    · intro N
      change _ = 𝟙 ((globalF D Sc i a ha Λ h).toFunctor.obj N)
      simp [globalActionUnit, globalActionCounit, SuperNatTrans.ofNatTrans,
        globalActionF, Superfunctor.map,
        Superfunctor.obj]
      exact (globalWeightAdjunction D Sc a ha i Λ h).right_triangle_components N
    · intro N
      simp [globalActionUnit, globalActionCounit, SuperNatTrans.ofNatTrans]

end Weight

end OddMath.QuiverHecke.CyclotomicAction
