/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightModules
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToAdjunction

/-! # The selected right adjunction of the global OLD probe

`SwappedActionAssembly` F1: assemble the exact balanced old append
unit and counit over all original-weight content blocks, including absent
predecessors. Both triangles and evenness are proved for all evaluated
module inputs; no factor-action or local-inversion premise is supplied.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
open ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

abbrev probeOldBlockAdj (β : WeightBlocks D Λ x) :
    (probeOldBlockInd D Sc m i Λ h β).toFunctor ⊣
      (probeOldBlockRes D Sc m i Λ h β).toFunctor :=
  probeAppendToAdjunction D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList _

/-- The unit component at a block of weight `x`. -/
def probeOldWeightUnitApp (β : WeightBlocks D Λ x) (M : ProbeOldWeightProduct D Sc m Λ x) :
    M β ⟶ (probeOldBlockRes D Sc m i Λ h β).obj
      ((probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).obj M) :=
  (probeOldBlockAdj D Sc m i Λ h β).unit.app (M β) ≫
    (probeOldBlockRes D Sc m i Λ h β).map
      (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm)

theorem probeOldWeightUnitApp_naturality (β : WeightBlocks D Λ x)
    {M M' : ProbeOldWeightProduct D Sc m Λ x} (f : M ⟶ M') :
    f β ≫ probeOldWeightUnitApp D Sc m i Λ h β M' =
      probeOldWeightUnitApp D Sc m i Λ h β M ≫ (probeOldBlockRes D Sc m i Λ h β).map
        ((probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [probeOldInductionComponent_map_blockSucc]
  simp only [probeOldWeightUnitApp, Superfunctor.map, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [Functor.map_comp, ← Adjunction.unit_naturality_assoc]

/-- The unit on weight spaces. -/
def probeOldWeightUnit : 𝟭 (ProbeOldWeightProduct D Sc m Λ x) ⟶
    probeOldEFunctor D Sc m i Λ h ⋙ (probeOldF D Sc m i Λ h).toFunctor where
  app M β := probeOldWeightUnitApp D Sc m i Λ h β M
  naturality _ _ f := funext fun β => probeOldWeightUnitApp_naturality D Sc m i Λ h β f

/-- The counit at a block with a chosen predecessor. -/
def probeOldWeightCounitVia (N : ProbeOldWeightProduct D Sc m Λ y) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj ((probeOldF D Sc m i Λ h).obj N) ⟶ N δ := by
  subst hβ
  exact eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β _) ≫
    (probeOldBlockAdj D Sc m i Λ h β).counit.app (N (blockSucc D Λ i h β))

theorem probeOldWeightCounitVia_eq (N : ProbeOldWeightProduct D Sc m Λ y) (β β' : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) (hβ' : blockSucc D Λ i h β' = δ) :
    probeOldWeightCounitVia D Sc m i Λ h N β δ hβ =
      probeOldWeightCounitVia D Sc m i Λ h N β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The counit component at a block: through the predecessor, or zero. -/
def probeOldWeightCounitComponent (N : ProbeOldWeightProduct D Sc m Λ y) (δ : WeightBlocks D Λ y) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj ((probeOldF D Sc m i Λ h).obj N) ⟶ N δ :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    probeOldWeightCounitVia D Sc m i Λ h N hδ.choose δ hδ.choose_spec
  else 0

theorem probeOldWeightCounitComponent_blockSucc (N : ProbeOldWeightProduct D Sc m Λ y)
    (β : WeightBlocks D Λ x) :
    probeOldWeightCounitComponent D Sc m i Λ h N (blockSucc D Λ i h β) =
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β
        ((probeOldF D Sc m i Λ h).obj N)) ≫
        (probeOldBlockAdj D Sc m i Λ h β).counit.app (N (blockSucc D Λ i h β)) := by
  unfold probeOldWeightCounitComponent
  split
  · rename_i hc
    exact probeOldWeightCounitVia_eq D Sc m i Λ h N _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem probeOldWeightCounitComponent_naturality (β : WeightBlocks D Λ x)
    {N N' : ProbeOldWeightProduct D Sc m Λ y} (g : N ⟶ N') :
    (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map
        ((probeOldF D Sc m i Λ h).map g) ≫
      probeOldWeightCounitComponent D Sc m i Λ h N' (blockSucc D Λ i h β) =
    probeOldWeightCounitComponent D Sc m i Λ h N (blockSucc D Λ i h β) ≫
      g (blockSucc D Λ i h β) := by
  rw [probeOldInductionComponent_map_blockSucc, probeOldWeightCounitComponent_blockSucc,
    probeOldWeightCounitComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  congr 1
  exact (probeOldBlockAdj D Sc m i Λ h β).counit_naturality (g (blockSucc D Λ i h β))

/-- The counit on weight spaces. -/
def probeOldWeightCounit : (probeOldF D Sc m i Λ h).toFunctor ⋙ probeOldEFunctor D Sc m i Λ h ⟶
    𝟭 (ProbeOldWeightProduct D Sc m Λ y) where
  app N δ := probeOldWeightCounitComponent D Sc m i Λ h N δ
  naturality N N' g := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact probeOldWeightCounitComponent_naturality D Sc m i Λ h β g
    · exact (probeOldInductionComponent_isZero D Sc m i Λ h δ hδ _).eq_of_src _ _

theorem probeOldWeight_left_triangle (β : WeightBlocks D Λ x) (M : ProbeOldWeightProduct D Sc m Λ x) :
    (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map
        ((probeOldWeightUnit D Sc m i Λ h).app M) ≫
      probeOldWeightCounitComponent D Sc m i Λ h ((probeOldEFunctor D Sc m i Λ h).obj M)
        (blockSucc D Λ i h β) = 𝟙 _ := by
  rw [probeOldInductionComponent_map_blockSucc, probeOldWeightCounitComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  change eqToHom _ ≫ (probeOldBlockInd D Sc m i Λ h β).map (probeOldWeightUnitApp D Sc m i Λ h β M) ≫
    _ = _
  simp only [probeOldWeightUnitApp, Superfunctor.map, Functor.map_comp, Category.assoc]
  erw [Adjunction.counit_naturality, Adjunction.left_triangle_components_assoc]
  simp

theorem probeOldWeight_right_triangle (β : WeightBlocks D Λ x) (N : ProbeOldWeightProduct D Sc m Λ y) :
    probeOldWeightUnitApp D Sc m i Λ h β ((probeOldF D Sc m i Λ h).obj N) ≫
      (probeOldBlockRes D Sc m i Λ h β).map
        (probeOldWeightCounitComponent D Sc m i Λ h N (blockSucc D Λ i h β)) = 𝟙 _ := by
  rw [probeOldWeightCounitComponent_blockSucc]
  simp only [probeOldWeightUnitApp, Superfunctor.map, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact (probeOldBlockAdj D Sc m i Λ h β).right_triangle_components _

/-- **Induction is left adjoint to restriction on weight spaces.** -/
def probeOldWeightAdjunction :
    probeOldEFunctor D Sc m i Λ h ⊣ (probeOldF D Sc m i Λ h).toFunctor where
  unit := probeOldWeightUnit D Sc m i Λ h
  counit := probeOldWeightCounit D Sc m i Λ h
  left_triangle_components M := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact probeOldWeight_left_triangle D Sc m i Λ h β M
    · exact (probeOldInductionComponent_isZero D Sc m i Λ h δ hδ _).eq_of_src _ _
  right_triangle_components N := funext fun β => probeOldWeight_right_triangle D Sc m i Λ h β N

theorem probeOldBlockAdj_unit_mem (β : WeightBlocks D Λ x)
    (M : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockAdj D Sc m i Λ h β).unit.app M ∈ parity (R := k) _ _ 0 :=
  probeAppendToAdjunction_unit_mem D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList _ M

theorem probeOldBlockAdj_counit_mem (β : WeightBlocks D Λ x)
    (M : ProbeCanonicalModules D Sc m (blockSucc D Λ i h β).1) :
    (probeOldBlockAdj D Sc m i Λ h β).counit.app M ∈ parity (R := k) _ _ 0 :=
  probeAppendToAdjunction_counit_mem D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList _ M

theorem probeOldWeightUnitApp_mem (β : WeightBlocks D Λ x) (M : ProbeOldWeightProduct D Sc m Λ x) :
    probeOldWeightUnitApp D Sc m i Λ h β M ∈ parity (R := k) _ _ 0 := by
  unfold probeOldWeightUnitApp
  rw [← zero_add (0 : ZMod 2)]
  exact comp_mem (probeOldBlockAdj_unit_mem D Sc m i Λ h β (M β))
    (IsSuperfunctor.map_mem (F := (probeOldBlockRes D Sc m i Λ h β).toFunctor)
      (eqToHom_mem_parity_zero (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm))

theorem probeOldWeightUnit_mem (M : ProbeOldWeightProduct D Sc m Λ x) :
    (probeOldWeightUnit D Sc m i Λ h).app M ∈ parity (R := k) _ _ 0 := fun β =>
  probeOldWeightUnitApp_mem D Sc m i Λ h β M

theorem probeOldWeightCounit_mem (M : ProbeOldWeightProduct D Sc m Λ y) :
    (probeOldWeightCounit D Sc m i Λ h).app M ∈ parity (R := k) _ _ 0 := fun δ => by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change probeOldWeightCounitComponent D Sc m i Λ h M (blockSucc D Λ i h β) ∈ _
    rw [probeOldWeightCounitComponent_blockSucc, ← zero_add (0 : ZMod 2)]
    exact comp_mem (eqToHom_mem_parity_zero (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β
        ((probeOldF D Sc m i Λ h).obj M)))
      (probeOldBlockAdj_counit_mem D Sc m i Λ h β (M (blockSucc D Λ i h β)))
  · rw [(probeOldInductionComponent_isZero D Sc m i Λ h δ hδ _).eq_of_src
      ((probeOldWeightCounit D Sc m i Λ h).app M δ) 0]
    exact Submodule.zero_mem _

/-- The actual OLD probe weight functors carry the prescribed even right adjunction. -/
def probeOldActionAdjunction :
    SKM.SuperAdjunction (k := k) (probeOldE D Sc m i Λ h) (probeOldF D Sc m i Λ h) :=
  ELVOld.ordinaryEvenSuperAdjunction (probeOldE D Sc m i Λ h) (probeOldF D Sc m i Λ h)
    (probeOldWeightAdjunction D Sc m i Λ h) (probeOldWeightUnit_mem D Sc m i Λ h)
    (probeOldWeightCounit_mem D Sc m i Λ h)

end OddMath.QuiverHecke
