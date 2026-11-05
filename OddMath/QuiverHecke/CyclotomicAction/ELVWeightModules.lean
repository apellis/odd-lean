/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModuleTransform
import OddMath.QuiverHecke.CyclotomicAction.PiWeightSpaces

/-! # Full-ELV module categories at every original weight

Advances `DeformedActionAssembly.md` §5. All blocks of the original weight
group are retained. Induction uses the actual full-coefficient content append
functor at the unique predecessor block, and the zero module on absent
predecessors. Restriction uses the same append functor. Their adjunction is
assembled from the concrete balanced induction adjunction, including the
absent-colour boundary. No local inversion, polynomial replacement, faithful
model or finite-colour assumption is used.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- The zero vector superspace used for genuinely absent content predecessors. -/
abbrev elvZeroSpace : SVec.{u} k where
  carrier := PUnit.{u + 1}
  odd := 0
  odd_comp_odd := LinearMap.ext fun _ => rfl

/-- The underlying zero-module functor, before bundling its super structure. -/
abbrev elvZeroModuleFunctor (β : Multiset I) :
    ContentCategory D Sc cutoff bound β ⥤ SVec.{u} k where
  obj := fun _ => elvZeroSpace (k := k)
  map := fun _ => 0
  map_id := by intro v; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
  map_comp := by intros; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _

instance (β : Multiset I) : (elvZeroModuleFunctor D Sc cutoff bound β).Additive where
  map_add := by intros; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
instance (β : Multiset I) : (elvZeroModuleFunctor D Sc cutoff bound β).Linear k where
  map_smul := by intros; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
instance (β : Multiset I) : IsSuperfunctor k (elvZeroModuleFunctor D Sc cutoff bound β) where
  map_mem _ := Submodule.zero_mem _

/-- The zero module on the existing exact-content category. -/
abbrev elvZeroModule (β : Multiset I) : ContentModules D Sc cutoff bound β :=
  ⟨elvZeroModuleFunctor D Sc cutoff bound β⟩

theorem elvZeroModule_isZero (β : Multiset I) :
    Limits.IsZero (elvZeroModule D Sc cutoff bound β) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply Superfunctor.hom_ext
  intro p v
  apply SVec.hom_ext
  intro x
  exact Subsingleton.elim _ _

section ZeroFunctor
variable {C : Type*} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]

def elvZeroFunctor (β : Multiset I) : C ⥤ ContentModules D Sc cutoff bound β :=
  (Functor.const C).obj (elvZeroModule D Sc cutoff bound β)

instance (β : Multiset I) : (elvZeroFunctor D Sc cutoff bound (C := C) β).Additive where
  map_add := (elvZeroModule_isZero D Sc cutoff bound β).eq_of_src _ _
instance (β : Multiset I) : (elvZeroFunctor D Sc cutoff bound (C := C) β).Linear k where
  map_smul _ _ := (elvZeroModule_isZero D Sc cutoff bound β).eq_of_src _ _
instance (β : Multiset I) : IsSuperfunctor k (elvZeroFunctor D Sc cutoff bound (C := C) β) where
  map_mem {_ _ _ f} _ := by
    rw [(elvZeroModule_isZero D Sc cutoff bound β).eq_of_src
      ((elvZeroFunctor D Sc cutoff bound β).map f) 0]
    exact Submodule.zero_mem _
end ZeroFunctor

/-- All content blocks of one original weight; no quotient of the weight group. -/
abbrev ELVWeightProduct (Λ x : X) :=
  ∀ β : WeightBlocks D Λ x, ContentModules D Sc cutoff bound β.1

@[instance_reducible]
def elvWeightPi (Λ x : X) : PiSupercategory k (ELVWeightProduct D Sc cutoff bound Λ x) :=
  letI := fun β : WeightBlocks D Λ x => contentModulesPi D Sc cutoff bound β.1
  productPiSupercategory _

abbrev elvWeightSpace (Λ x : X) : PiSCat.{u, u, u + 1} k :=
  letI := elvWeightPi D Sc cutoff bound Λ x
  PiSCat.of k (ELVWeightProduct D Sc cutoff bound Λ x)

section Weight
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The actual append functor between a block and its exact successor. -/
abbrev elvBlockAppend (β : WeightBlocks D Λ x) :=
  contentAppendTo D Sc cutoff bound β.1 [i] (blockSucc D Λ i h β).1
    (by rw [blockSucc_val, add_comm]; rfl)

abbrev elvBlockInd (β : WeightBlocks D Λ x) :
    Superfunctor k (ContentModules D Sc cutoff bound β.1)
      (ContentModules D Sc cutoff bound (blockSucc D Λ i h β).1) :=
  ⟨BalancedInduction.induction (elvBlockAppend D Sc cutoff bound i Λ h β)⟩

abbrev elvBlockRes (β : WeightBlocks D Λ x) :
    Superfunctor k (ContentModules D Sc cutoff bound (blockSucc D Λ i h β).1)
      (ContentModules D Sc cutoff bound β.1) :=
  ⟨BalancedInduction.restriction (elvBlockAppend D Sc cutoff bound i Λ h β)⟩

abbrev elvBlockAdj (β : WeightBlocks D Λ x) :
    (elvBlockInd D Sc cutoff bound i Λ h β).toFunctor ⊣
      (elvBlockRes D Sc cutoff bound i Λ h β).toFunctor :=
  BalancedInduction.adjunction (elvBlockAppend D Sc cutoff bound i Λ h β)

def elvBlockEval (β : WeightBlocks D Λ x) :
    Superfunctor k (ELVWeightProduct D Sc cutoff bound Λ x)
      (ContentModules D Sc cutoff bound β.1) := ⟨Pi.eval _ β⟩

private def elvInductionVia (δ : WeightBlocks D Λ y) (β : WeightBlocks D Λ x)
    (hβ : blockSucc D Λ i h β = δ) :
    Superfunctor k (ELVWeightProduct D Sc cutoff bound Λ x)
      (ContentModules D Sc cutoff bound δ.1) := by
  subst δ
  exact (elvBlockEval D Sc cutoff bound Λ β).comp (elvBlockInd D Sc cutoff bound i Λ h β)

private theorem elvInductionVia_eq (δ : WeightBlocks D Λ y)
    (β β' : WeightBlocks D Λ x) (hβ : blockSucc D Λ i h β = δ)
    (hβ' : blockSucc D Λ i h β' = δ) :
    elvInductionVia D Sc cutoff bound i Λ h δ β hβ =
      elvInductionVia D Sc cutoff bound i Λ h δ β' hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  rfl

def elvInductionComponent (δ : WeightBlocks D Λ y) :
    Superfunctor k (ELVWeightProduct D Sc cutoff bound Λ x)
      (ContentModules D Sc cutoff bound δ.1) :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    elvInductionVia D Sc cutoff bound i Λ h δ hδ.choose hδ.choose_spec
  else ⟨elvZeroFunctor D Sc cutoff bound δ.1⟩

theorem elvInductionComponent_blockSucc (β : WeightBlocks D Λ x) :
    elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β) =
      (elvBlockEval D Sc cutoff bound Λ β).comp (elvBlockInd D Sc cutoff bound i Λ h β) := by
  unfold elvInductionComponent
  split
  · rename_i hc
    exact elvInductionVia_eq D Sc cutoff bound i Λ h _ _ β hc.choose_spec rfl
  · rename_i hn
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hn

theorem elvInductionComponent_isZero (δ : WeightBlocks D Λ y)
    (hδ : ¬ ∃ β, blockSucc D Λ i h β = δ)
    (M : ELVWeightProduct D Sc cutoff bound Λ x) :
    Limits.IsZero ((elvInductionComponent D Sc cutoff bound i Λ h δ).obj M) := by
  unfold elvInductionComponent
  split
  · exact absurd ‹_› hδ
  · exact elvZeroModule_isZero D Sc cutoff bound δ.1

def elvEFunctor : ELVWeightProduct D Sc cutoff bound Λ x ⥤
    ELVWeightProduct D Sc cutoff bound Λ y :=
  Functor.pi' fun δ => (elvInductionComponent D Sc cutoff bound i Λ h δ).toFunctor

instance : (elvEFunctor D Sc cutoff bound i Λ h).Additive where
  map_add := funext fun δ => (elvInductionComponent D Sc cutoff bound i Λ h δ).toFunctor.map_add
instance : (elvEFunctor D Sc cutoff bound i Λ h).Linear k where
  map_smul f r := funext fun δ =>
    (elvInductionComponent D Sc cutoff bound i Λ h δ).toFunctor.map_smul r f
instance : IsSuperfunctor k (elvEFunctor D Sc cutoff bound i Λ h) where
  map_mem hf δ := IsSuperfunctor.map_mem
    (F := (elvInductionComponent D Sc cutoff bound i Λ h δ).toFunctor) hf

def elvE : elvWeightSpace D Sc cutoff bound Λ x ⟶ elvWeightSpace D Sc cutoff bound Λ y :=
  ⟨elvEFunctor D Sc cutoff bound i Λ h⟩

def elvF : elvWeightSpace D Sc cutoff bound Λ y ⟶ elvWeightSpace D Sc cutoff bound Λ x :=
  ⟨productFunctor (fun δ : WeightBlocks D Λ y => ContentModules D Sc cutoff bound δ.1)
    (blockSucc D Λ i h) (fun β : WeightBlocks D Λ x => ContentModules D Sc cutoff bound β.1)
    (fun β => (elvBlockRes D Sc cutoff bound i Λ h β).toFunctor)⟩

theorem elvInductionComponent_obj_blockSucc (β : WeightBlocks D Λ x)
    (M : ELVWeightProduct D Sc cutoff bound Λ x) :
    (elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).obj M =
      (elvBlockInd D Sc cutoff bound i Λ h β).obj (M β) := by
  rw [elvInductionComponent_blockSucc]
  rfl

theorem elvInductionComponent_map_blockSucc (β : WeightBlocks D Λ x)
    {M M' : ELVWeightProduct D Sc cutoff bound Λ x} (f : M ⟶ M') :
    (elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).map f =
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M) ≫
        (elvBlockInd D Sc cutoff bound i Λ h β).map (f β) ≫
          eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M').symm :=
  superfunctor_map_of_eq (elvInductionComponent_blockSucc D Sc cutoff bound i Λ h β) f

/-- The unit component at a block of weight `x`. -/
def elvWeightUnitApp (β : WeightBlocks D Λ x) (M : ELVWeightProduct D Sc cutoff bound Λ x) :
    M β ⟶ (elvBlockRes D Sc cutoff bound i Λ h β).obj
      ((elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).obj M) :=
  (elvBlockAdj D Sc cutoff bound i Λ h β).unit.app (M β) ≫
    (elvBlockRes D Sc cutoff bound i Λ h β).map
      (eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M).symm)

theorem elvWeightUnitApp_naturality (β : WeightBlocks D Λ x)
    {M M' : ELVWeightProduct D Sc cutoff bound Λ x} (f : M ⟶ M') :
    f β ≫ elvWeightUnitApp D Sc cutoff bound i Λ h β M' =
      elvWeightUnitApp D Sc cutoff bound i Λ h β M ≫ (elvBlockRes D Sc cutoff bound i Λ h β).map
        ((elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [elvInductionComponent_map_blockSucc]
  simp only [elvWeightUnitApp, Superfunctor.map, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [Functor.map_comp, ← Adjunction.unit_naturality_assoc]

/-- The unit on weight spaces. -/
def elvWeightUnit : 𝟭 (ELVWeightProduct D Sc cutoff bound Λ x) ⟶
    elvEFunctor D Sc cutoff bound i Λ h ⋙ (elvF D Sc cutoff bound i Λ h).toFunctor where
  app M β := elvWeightUnitApp D Sc cutoff bound i Λ h β M
  naturality _ _ f := funext fun β => elvWeightUnitApp_naturality D Sc cutoff bound i Λ h β f

/-- The counit at a block with a chosen predecessor. -/
def elvWeightCounitVia (N : ELVWeightProduct D Sc cutoff bound Λ y) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (elvInductionComponent D Sc cutoff bound i Λ h δ).obj ((elvF D Sc cutoff bound i Λ h).obj N) ⟶ N δ := by
  subst hβ
  exact eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β _) ≫
    (elvBlockAdj D Sc cutoff bound i Λ h β).counit.app (N (blockSucc D Λ i h β))

theorem elvWeightCounitVia_eq (N : ELVWeightProduct D Sc cutoff bound Λ y) (β β' : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) (hβ' : blockSucc D Λ i h β' = δ) :
    elvWeightCounitVia D Sc cutoff bound i Λ h N β δ hβ =
      elvWeightCounitVia D Sc cutoff bound i Λ h N β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The counit component at a block: through the predecessor, or zero. -/
def elvWeightCounitComponent (N : ELVWeightProduct D Sc cutoff bound Λ y) (δ : WeightBlocks D Λ y) :
    (elvInductionComponent D Sc cutoff bound i Λ h δ).obj ((elvF D Sc cutoff bound i Λ h).obj N) ⟶ N δ :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    elvWeightCounitVia D Sc cutoff bound i Λ h N hδ.choose δ hδ.choose_spec
  else 0

theorem elvWeightCounitComponent_blockSucc (N : ELVWeightProduct D Sc cutoff bound Λ y)
    (β : WeightBlocks D Λ x) :
    elvWeightCounitComponent D Sc cutoff bound i Λ h N (blockSucc D Λ i h β) =
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β
        ((elvF D Sc cutoff bound i Λ h).obj N)) ≫
        (elvBlockAdj D Sc cutoff bound i Λ h β).counit.app (N (blockSucc D Λ i h β)) := by
  unfold elvWeightCounitComponent
  split
  · rename_i hc
    exact elvWeightCounitVia_eq D Sc cutoff bound i Λ h N _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem elvWeightCounitComponent_naturality (β : WeightBlocks D Λ x)
    {N N' : ELVWeightProduct D Sc cutoff bound Λ y} (g : N ⟶ N') :
    (elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).map
        ((elvF D Sc cutoff bound i Λ h).map g) ≫
      elvWeightCounitComponent D Sc cutoff bound i Λ h N' (blockSucc D Λ i h β) =
    elvWeightCounitComponent D Sc cutoff bound i Λ h N (blockSucc D Λ i h β) ≫
      g (blockSucc D Λ i h β) := by
  rw [elvInductionComponent_map_blockSucc, elvWeightCounitComponent_blockSucc,
    elvWeightCounitComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  congr 1
  exact (elvBlockAdj D Sc cutoff bound i Λ h β).counit_naturality (g (blockSucc D Λ i h β))

/-- The counit on weight spaces. -/
def elvWeightCounit : (elvF D Sc cutoff bound i Λ h).toFunctor ⋙ elvEFunctor D Sc cutoff bound i Λ h ⟶
    𝟭 (ELVWeightProduct D Sc cutoff bound Λ y) where
  app N δ := elvWeightCounitComponent D Sc cutoff bound i Λ h N δ
  naturality N N' g := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact elvWeightCounitComponent_naturality D Sc cutoff bound i Λ h β g
    · exact (elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ _).eq_of_src _ _

theorem elvWeight_left_triangle (β : WeightBlocks D Λ x) (M : ELVWeightProduct D Sc cutoff bound Λ x) :
    (elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).map
        ((elvWeightUnit D Sc cutoff bound i Λ h).app M) ≫
      elvWeightCounitComponent D Sc cutoff bound i Λ h ((elvEFunctor D Sc cutoff bound i Λ h).obj M)
        (blockSucc D Λ i h β) = 𝟙 _ := by
  rw [elvInductionComponent_map_blockSucc, elvWeightCounitComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  change eqToHom _ ≫ (elvBlockInd D Sc cutoff bound i Λ h β).map (elvWeightUnitApp D Sc cutoff bound i Λ h β M) ≫
    _ = _
  simp only [elvWeightUnitApp, Superfunctor.map, Functor.map_comp, Category.assoc]
  erw [Adjunction.counit_naturality, Adjunction.left_triangle_components_assoc]
  simp

theorem elvWeight_right_triangle (β : WeightBlocks D Λ x) (N : ELVWeightProduct D Sc cutoff bound Λ y) :
    elvWeightUnitApp D Sc cutoff bound i Λ h β ((elvF D Sc cutoff bound i Λ h).obj N) ≫
      (elvBlockRes D Sc cutoff bound i Λ h β).map
        (elvWeightCounitComponent D Sc cutoff bound i Λ h N (blockSucc D Λ i h β)) = 𝟙 _ := by
  rw [elvWeightCounitComponent_blockSucc]
  simp only [elvWeightUnitApp, Superfunctor.map, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact (elvBlockAdj D Sc cutoff bound i Λ h β).right_triangle_components _

/-- **Induction is left adjoint to restriction on weight spaces.** -/
def elvWeightAdjunction :
    elvEFunctor D Sc cutoff bound i Λ h ⊣ (elvF D Sc cutoff bound i Λ h).toFunctor where
  unit := elvWeightUnit D Sc cutoff bound i Λ h
  counit := elvWeightCounit D Sc cutoff bound i Λ h
  left_triangle_components M := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact elvWeight_left_triangle D Sc cutoff bound i Λ h β M
    · exact (elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ _).eq_of_src _ _
  right_triangle_components N := funext fun β => elvWeight_right_triangle D Sc cutoff bound i Λ h β N

theorem elvBlockAdj_unit_mem (β : WeightBlocks D Λ x)
    (M : ContentModules D Sc cutoff bound β.1) :
    (elvBlockAdj D Sc cutoff bound i Λ h β).unit.app M ∈ parity (R := k) _ _ 0 := by
  change (BalancedInduction.unitTransform (elvBlockAppend D Sc cutoff bound i Λ h β) M).app 1 = 0
  funext w
  simp only [BalancedInduction.unitTransform_app, one_ne_zero, ↓reduceIte, Pi.zero_apply]

theorem elvBlockAdj_counit_mem (β : WeightBlocks D Λ x)
    (M : ContentModules D Sc cutoff bound (blockSucc D Λ i h β).1) :
    (elvBlockAdj D Sc cutoff bound i Λ h β).counit.app M ∈ parity (R := k) _ _ 0 := by
  change (BalancedInduction.counitTransform (elvBlockAppend D Sc cutoff bound i Λ h β) M).app 1 = 0
  funext w
  simp only [BalancedInduction.counitTransform_app, one_ne_zero, ↓reduceIte, Pi.zero_apply]

theorem elvWeightUnitApp_mem (β : WeightBlocks D Λ x) (M : ELVWeightProduct D Sc cutoff bound Λ x) :
    elvWeightUnitApp D Sc cutoff bound i Λ h β M ∈ parity (R := k) _ _ 0 := by
  unfold elvWeightUnitApp
  rw [← zero_add (0 : ZMod 2)]
  exact comp_mem (elvBlockAdj_unit_mem D Sc cutoff bound i Λ h β (M β))
    (IsSuperfunctor.map_mem (F := (elvBlockRes D Sc cutoff bound i Λ h β).toFunctor)
      (eqToHom_mem_parity_zero (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M).symm))

theorem elvWeightUnit_mem (M : ELVWeightProduct D Sc cutoff bound Λ x) :
    (elvWeightUnit D Sc cutoff bound i Λ h).app M ∈ parity (R := k) _ _ 0 := fun β =>
  elvWeightUnitApp_mem D Sc cutoff bound i Λ h β M

theorem elvWeightCounit_mem (M : ELVWeightProduct D Sc cutoff bound Λ y) :
    (elvWeightCounit D Sc cutoff bound i Λ h).app M ∈ parity (R := k) _ _ 0 := fun δ => by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change elvWeightCounitComponent D Sc cutoff bound i Λ h M (blockSucc D Λ i h β) ∈ _
    rw [elvWeightCounitComponent_blockSucc, ← zero_add (0 : ZMod 2)]
    exact comp_mem (eqToHom_mem_parity_zero (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β
        ((elvF D Sc cutoff bound i Λ h).obj M)))
      (elvBlockAdj_counit_mem D Sc cutoff bound i Λ h β (M (blockSucc D Λ i h β)))
  · rw [(elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ _).eq_of_src
      ((elvWeightCounit D Sc cutoff bound i Λ h).app M δ) 0]
    exact Submodule.zero_mem _

end Weight
end OddMath.QuiverHecke.ELVOld
