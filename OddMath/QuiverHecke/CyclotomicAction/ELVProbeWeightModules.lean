/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCanonicalContent
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightModules

/-! # The scalar-evaluated OLD probe at every weight

`SwappedDetectingFamily` §2: retain every multiset block of the original
weight group. Chosen old append induction acts at its unique predecessor,
with the zero evaluated module when no predecessor exists. Restriction
uses the same old append. No root-map injectivity or finiteness is assumed.
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

/-- The zero functor on the actual OLD canonical content category. -/
abbrev probeOldZeroModuleFunctor (β : Multiset I) :
    OldContentCategory D Sc (probeCutoff D m) β.toList ⥤ SVec.{u} k where
  obj := fun _ => elvZeroSpace (k := k)
  map := fun _ => 0
  map_id := by intro v; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
  map_comp := by intros; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _

instance (β : Multiset I) : (probeOldZeroModuleFunctor D Sc m β).Additive where
  map_add := by intros; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
instance (β : Multiset I) : (probeOldZeroModuleFunctor D Sc m β).Linear k where
  map_smul := by intros; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
instance (β : Multiset I) : IsSuperfunctor k (probeOldZeroModuleFunctor D Sc m β) where
  map_mem _ := Submodule.zero_mem _

/-- An absent predecessor contributes the genuine zero scalar-evaluated module. -/
abbrev probeOldZeroModule (β : Multiset I) : ProbeCanonicalModules D Sc m β :=
  ⟨⟨probeOldZeroModuleFunctor D Sc m β⟩, by
    intro v c
    apply SVec.hom_ext
    intro x
    exact Subsingleton.elim _ _⟩

theorem probeOldZeroModule_isZero (β : Multiset I) :
    Limits.IsZero (probeOldZeroModule D Sc m β) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply InducedCategory.hom_ext
  apply Superfunctor.hom_ext
  intro p v
  apply SVec.hom_ext
  intro x
  exact Subsingleton.elim _ _

section ZeroFunctor
variable {C : Type*} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]

def probeOldZeroFunctor (β : Multiset I) : C ⥤ ProbeCanonicalModules D Sc m β :=
  (Functor.const C).obj (probeOldZeroModule D Sc m β)

instance (β : Multiset I) : (probeOldZeroFunctor D Sc m (C := C) β).Additive where
  map_add := (probeOldZeroModule_isZero D Sc m β).eq_of_src _ _
instance (β : Multiset I) : (probeOldZeroFunctor D Sc m (C := C) β).Linear k where
  map_smul _ _ := (probeOldZeroModule_isZero D Sc m β).eq_of_src _ _
instance (β : Multiset I) : IsSuperfunctor k (probeOldZeroFunctor D Sc m (C := C) β) where
  map_mem {_ _ _ f} _ := by
    rw [(probeOldZeroModule_isZero D Sc m β).eq_of_src
      ((probeOldZeroFunctor D Sc m β).map f) 0]
    exact Submodule.zero_mem _
end ZeroFunctor

/-- All content blocks of one original weight; no quotient of the weight group. -/
abbrev ProbeOldWeightProduct (Λ x : X) :=
  ∀ β : WeightBlocks D Λ x, ProbeCanonicalModules D Sc m β.1

@[instance_reducible]
def probeOldWeightPi (Λ x : X) : PiSupercategory k (ProbeOldWeightProduct D Sc m Λ x) :=
  letI := fun β : WeightBlocks D Λ x => probeCanonicalPiSupercategory D Sc m β.1
  productPiSupercategory _

abbrev probeOldWeightSpace (Λ x : X) : PiSCat.{u, u, u + 1} k :=
  letI := probeOldWeightPi D Sc m Λ x
  PiSCat.of k (ProbeOldWeightProduct D Sc m Λ x)

section Weight
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The selected append between actual OLD multiset representatives. -/
abbrev probeOldBlockAppend (β : WeightBlocks D Λ x) :=
  oldContentAppendTo D Sc (probeCutoff D m) β.1.toList i
    (blockSucc D Λ i h β).1.toList
    (by
      apply Multiset.coe_eq_coe.mp
      rw [Multiset.coe_toList]
      change {i} + (β.1.toList : Multiset I) = (blockSucc D Λ i h β).1
      rw [Multiset.coe_toList, blockSucc_val])

abbrev probeOldBlockInd (β : WeightBlocks D Λ x) :
    Superfunctor k (ProbeCanonicalModules D Sc m β.1)
      (ProbeCanonicalModules D Sc m (blockSucc D Λ i h β).1) :=
  ⟨probeEvaluatedAppendTo D Sc m β.1.toList i (blockSucc D Λ i h β).1.toList
    (by
      apply Multiset.coe_eq_coe.mp
      rw [Multiset.coe_toList]
      change {i} + (β.1.toList : Multiset I) = (blockSucc D Λ i h β).1
      rw [Multiset.coe_toList, blockSucc_val])⟩

abbrev probeOldBlockRes (β : WeightBlocks D Λ x) :
    Superfunctor k (ProbeCanonicalModules D Sc m (blockSucc D Λ i h β).1)
      (ProbeCanonicalModules D Sc m β.1) :=
  ⟨probeEvaluatedRestrictTo D Sc m β.1.toList i (blockSucc D Λ i h β).1.toList
    (by
      apply Multiset.coe_eq_coe.mp
      rw [Multiset.coe_toList]
      change {i} + (β.1.toList : Multiset I) = (blockSucc D Λ i h β).1
      rw [Multiset.coe_toList, blockSucc_val])⟩

def probeOldBlockEval (β : WeightBlocks D Λ x) :
    Superfunctor k (ProbeOldWeightProduct D Sc m Λ x)
      (ProbeCanonicalModules D Sc m β.1) := ⟨Pi.eval _ β⟩

private def probeOldInductionVia (δ : WeightBlocks D Λ y) (β : WeightBlocks D Λ x)
    (hβ : blockSucc D Λ i h β = δ) :
    Superfunctor k (ProbeOldWeightProduct D Sc m Λ x)
      (ProbeCanonicalModules D Sc m δ.1) := by
  subst δ
  exact (probeOldBlockEval D Sc m Λ β).comp (probeOldBlockInd D Sc m i Λ h β)

private theorem probeOldInductionVia_eq (δ : WeightBlocks D Λ y)
    (β β' : WeightBlocks D Λ x) (hβ : blockSucc D Λ i h β = δ)
    (hβ' : blockSucc D Λ i h β' = δ) :
    probeOldInductionVia D Sc m i Λ h δ β hβ =
      probeOldInductionVia D Sc m i Λ h δ β' hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  rfl

def probeOldInductionComponent (δ : WeightBlocks D Λ y) :
    Superfunctor k (ProbeOldWeightProduct D Sc m Λ x)
      (ProbeCanonicalModules D Sc m δ.1) :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    probeOldInductionVia D Sc m i Λ h δ hδ.choose hδ.choose_spec
  else ⟨probeOldZeroFunctor D Sc m δ.1⟩

theorem probeOldInductionComponent_blockSucc (β : WeightBlocks D Λ x) :
    probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β) =
      (probeOldBlockEval D Sc m Λ β).comp (probeOldBlockInd D Sc m i Λ h β) := by
  unfold probeOldInductionComponent
  split
  · rename_i hc
    exact probeOldInductionVia_eq D Sc m i Λ h _ _ β hc.choose_spec rfl
  · rename_i hn
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hn

theorem probeOldInductionComponent_isZero (δ : WeightBlocks D Λ y)
    (hδ : ¬ ∃ β, blockSucc D Λ i h β = δ)
    (M : ProbeOldWeightProduct D Sc m Λ x) :
    Limits.IsZero ((probeOldInductionComponent D Sc m i Λ h δ).obj M) := by
  unfold probeOldInductionComponent
  split
  · exact absurd ‹_› hδ
  · exact probeOldZeroModule_isZero D Sc m δ.1

def probeOldEFunctor : ProbeOldWeightProduct D Sc m Λ x ⥤
    ProbeOldWeightProduct D Sc m Λ y :=
  Functor.pi' fun δ => (probeOldInductionComponent D Sc m i Λ h δ).toFunctor

instance : (probeOldEFunctor D Sc m i Λ h).Additive where
  map_add := funext fun δ => (probeOldInductionComponent D Sc m i Λ h δ).toFunctor.map_add
instance : (probeOldEFunctor D Sc m i Λ h).Linear k where
  map_smul f r := funext fun δ =>
    (probeOldInductionComponent D Sc m i Λ h δ).toFunctor.map_smul r f
instance : IsSuperfunctor k (probeOldEFunctor D Sc m i Λ h) where
  map_mem hf δ := IsSuperfunctor.map_mem
    (F := (probeOldInductionComponent D Sc m i Λ h δ).toFunctor) hf

def probeOldE : probeOldWeightSpace D Sc m Λ x ⟶ probeOldWeightSpace D Sc m Λ y :=
  ⟨probeOldEFunctor D Sc m i Λ h⟩

def probeOldF : probeOldWeightSpace D Sc m Λ y ⟶ probeOldWeightSpace D Sc m Λ x :=
  ⟨productFunctor (fun δ : WeightBlocks D Λ y => ProbeCanonicalModules D Sc m δ.1)
    (blockSucc D Λ i h) (fun β : WeightBlocks D Λ x => ProbeCanonicalModules D Sc m β.1)
    (fun β => (probeOldBlockRes D Sc m i Λ h β).toFunctor)⟩

theorem probeOldInductionComponent_obj_blockSucc (β : WeightBlocks D Λ x)
    (M : ProbeOldWeightProduct D Sc m Λ x) :
    (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).obj M =
      (probeOldBlockInd D Sc m i Λ h β).obj (M β) := by
  rw [probeOldInductionComponent_blockSucc]
  rfl

theorem probeOldInductionComponent_map_blockSucc (β : WeightBlocks D Λ x)
    {M M' : ProbeOldWeightProduct D Sc m Λ x} (f : M ⟶ M') :
    (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map f =
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M) ≫
        (probeOldBlockInd D Sc m i Λ h β).map (f β) ≫
          eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M').symm :=
  superfunctor_map_of_eq (probeOldInductionComponent_blockSucc D Sc m i Λ h β) f

end Weight
end OddMath.QuiverHecke
