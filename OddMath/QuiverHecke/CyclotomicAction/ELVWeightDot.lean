/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightModules
import OddMath.QuiverHecke.CyclotomicAction.ELVContentInductionNilpotence

/-! # The normalized full-ELV dot on original-weight induction

The existing contentInductionDot is transported to the actual common successor
content, then assembled on the existing product of content module categories.
This construction asserts no uniform nilpotence exponent over a weight fibre.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

section Weight
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The existing normalized content dot, with a specified common target. -/
abbrev elvContentDotTo (β γ : Multiset I) (hγ : β + ([i] : Multiset I) = γ) :=
  contentInductionTransform D Sc cutoff bound hγ hγ (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

/-- The normalized content dot between a block and its successor. -/
abbrev elvBlockDot (β : WeightBlocks D Λ x) :=
  elvContentDotTo D Sc cutoff bound i β.1 (blockSucc D Λ i h β).1
    (by rw [blockSucc_val, add_comm]; rfl)

theorem elvBlockDot_homogeneous (β : WeightBlocks D Λ x) :
    (elvBlockDot D Sc cutoff bound i Λ h β).IsHomogeneous (D.parity i) := by
  exact (BalancedInduction.transformComponent_supernatural
    (contentAppendTo_supernatural D Sc cutoff bound
      (by rw [blockSucc_val, add_comm]; rfl)
      (by rw [blockSucc_val, add_comm]; rfl)
      (by simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1))).toSuperNatTrans_isHomogeneous

/-- Fixed-content nilpotence of the exact normalized dot. Its exponent may
depend on the source content, and is uniform in the arbitrary input module. -/
theorem elvContentDotTo_isNilpotent [Finite I] (sy : SKM.Symmetrizer D)
    (hc : Sc.Homogeneous) (β γ : Multiset I)
    (hγ : β + ([i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff bound β) :
    IsNilpotent (show End ((contentInductionTo D Sc cutoff bound β [i] γ hγ).obj M) from
      (elvContentDotTo D Sc cutoff bound i β γ hγ).app (D.parity i) M) := by
  classical
  subst γ
  change IsNilpotent (show End ((contentE D Sc cutoff bound β i).obj M) from
    (contentInductionDot D Sc cutoff bound β i).app (D.parity i) M)
  have hp := contentInductionDot_module_pow_zero D Sc cutoff sy hc bound β.toList i
  rw [Multiset.coe_toList] at hp
  obtain ⟨e, _, hp⟩ := hp
  exact ⟨e, hp M⟩

theorem elvBlockDot_isNilpotent [Finite I] (sy : SKM.Symmetrizer D)
    (hc : Sc.Homogeneous) (β : WeightBlocks D Λ x)
    (M : ContentModules D Sc cutoff bound β.1) :
    IsNilpotent (show End ((elvBlockInd D Sc cutoff bound i Λ h β).obj M) from
      (elvBlockDot D Sc cutoff bound i Λ h β).app (D.parity i) M) :=
  elvContentDotTo_isNilpotent D Sc cutoff bound i sy hc β.1
    (blockSucc D Λ i h β).1 (by rw [blockSucc_val, add_comm]; rfl) M

/-- The dot component at a block with a chosen predecessor. -/
def elvWeightDotVia (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff bound Λ x) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (elvInductionComponent D Sc cutoff bound i Λ h δ).obj M ⟶ (elvInductionComponent D Sc cutoff bound i Λ h δ).obj M := by
  subst hβ
  exact eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M) ≫
    (elvBlockDot D Sc cutoff bound i Λ h β).app p (M β) ≫
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M).symm

theorem elvWeightDotVia_eq (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff bound Λ x)
    (β β' : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ)
    (hβ' : blockSucc D Λ i h β' = δ) :
    elvWeightDotVia D Sc cutoff bound i Λ h p M β δ hβ =
      elvWeightDotVia D Sc cutoff bound i Λ h p M β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The dot component at a block: through the predecessor, or zero. -/
def elvWeightDotComponent (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff bound Λ x)
    (δ : WeightBlocks D Λ y) :
    (elvInductionComponent D Sc cutoff bound i Λ h δ).obj M ⟶ (elvInductionComponent D Sc cutoff bound i Λ h δ).obj M :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    elvWeightDotVia D Sc cutoff bound i Λ h p M hδ.choose δ hδ.choose_spec
  else 0

theorem elvWeightDotComponent_blockSucc (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff bound Λ x)
    (β : WeightBlocks D Λ x) :
    elvWeightDotComponent D Sc cutoff bound i Λ h p M (blockSucc D Λ i h β) =
      eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M) ≫
        (elvBlockDot D Sc cutoff bound i Λ h β).app p (M β) ≫
          eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M).symm := by
  unfold elvWeightDotComponent
  split
  · rename_i hc
    exact elvWeightDotVia_eq D Sc cutoff bound i Λ h p M _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem elvWeightDotComponent_mem (p : ZMod 2) (M : ELVWeightProduct D Sc cutoff bound Λ x)
    (δ : WeightBlocks D Λ y) :
    elvWeightDotComponent D Sc cutoff bound i Λ h p M δ ∈ parity (R := k) _ _ p := by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    rw [elvWeightDotComponent_blockSucc]
    have hm := comp_mem (eqToHom_mem_parity_zero
        (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M))
      (comp_mem ((elvBlockDot D Sc cutoff bound i Λ h β).app_mem p (M β))
        (eqToHom_mem_parity_zero (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M).symm))
    simpa only [zero_add, add_zero] using hm
  · rw [(elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ M).eq_of_src
      (elvWeightDotComponent D Sc cutoff bound i Λ h p M δ) 0]
    exact Submodule.zero_mem _

theorem elvWeightDotComponent_naturality (p : ZMod 2) (β : WeightBlocks D Λ x)
    {M M' : ELVWeightProduct D Sc cutoff bound Λ x} {q : ZMod 2} (f : M ⟶ M')
    (hf : f ∈ parity (R := k) M M' q) :
    (elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).map f ≫
        elvWeightDotComponent D Sc cutoff bound i Λ h p M' (blockSucc D Λ i h β) =
      koszulSign p q • (elvWeightDotComponent D Sc cutoff bound i Λ h p M (blockSucc D Λ i h β) ≫
        (elvInductionComponent D Sc cutoff bound i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [elvInductionComponent_map_blockSucc, elvWeightDotComponent_blockSucc,
    elvWeightDotComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hn := (elvBlockDot D Sc cutoff bound i Λ h β).naturality p (f β) (hf β)
  rw [← Category.assoc ((elvBlockInd D Sc cutoff bound i Λ h β).map (f β)), Superfunctor.map, hn,
    Linear.smul_comp, Linear.comp_smul, Category.assoc]

/-- **The dot on weight-space induction.** -/
def elvWeightDot :
    SuperNatTrans k (elvEFunctor D Sc cutoff bound i Λ h) (elvEFunctor D Sc cutoff bound i Λ h) where
  app p M δ := elvWeightDotComponent D Sc cutoff bound i Λ h p M δ
  app_mem p M δ := elvWeightDotComponent_mem D Sc cutoff bound i Λ h p M δ
  naturality p M M' q f hf := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact elvWeightDotComponent_naturality D Sc cutoff bound i Λ h p β f hf
    · exact (elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ _).eq_of_src _ _

private theorem end_isNilpotent_eqToHom_conj
    {C : Type*} [Category C] [Preadditive C]
    {M N : C} (e : M = N) (d : End N) (hd : IsNilpotent d) :
    IsNilpotent (show End M from eqToHom e ≫ d ≫ eqToHom e.symm) := by
  subst e
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hd

/-- The actual dot is nilpotent at each original target-weight content block.
There is deliberately no common exponent over the weight fibre. -/
theorem elvWeightDotComponent_isNilpotent [Finite I] (sy : SKM.Symmetrizer D)
    (hc : Sc.Homogeneous) (M : ELVWeightProduct D Sc cutoff bound Λ x)
    (δ : WeightBlocks D Λ y) :
    IsNilpotent (show End ((elvInductionComponent D Sc cutoff bound i Λ h δ).obj M) from
      elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M δ) := by
  classical
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    rw [elvWeightDotComponent_blockSucc]
    exact end_isNilpotent_eqToHom_conj
      (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h β M) _
      (elvBlockDot_isNilpotent D Sc cutoff bound i Λ h sy hc β (M β))
  · rw [(elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ M).eq_of_src
      (elvWeightDotComponent D Sc cutoff bound i Λ h (D.parity i) M δ) 0]
    exact ⟨1, by simp⟩

/-- Only the component of the colour parity is nonzero. -/
theorem elvWeightDot_homogeneous :
    (elvWeightDot D Sc cutoff bound i Λ h).IsHomogeneous (D.parity i) := by
  intro q hq
  funext M
  funext δ
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change elvWeightDotComponent D Sc cutoff bound i Λ h q M (blockSucc D Λ i h β) = 0
    rw [elvWeightDotComponent_blockSucc,
      congrFun (elvBlockDot_homogeneous D Sc cutoff bound i Λ h β q hq)
        (M β)]
    simp
  · exact (elvInductionComponent_isZero D Sc cutoff bound i Λ h δ hδ M).eq_of_src _ _

/-- The dot as a 2-endomorphism of weight-space induction in the action target. -/
def elvActionDot : elvE D Sc cutoff bound i Λ h ⟶ elvE D Sc cutoff bound i Λ h :=
  elvWeightDot D Sc cutoff bound i Λ h

/-- The dot has the parity of its colour, including for odd colours. -/
theorem elvActionDot_mem :
    elvActionDot D Sc cutoff bound i Λ h ∈
      parity (R := k) (elvE D Sc cutoff bound i Λ h) (elvE D Sc cutoff bound i Λ h)
        (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.2 (elvWeightDot_homogeneous D Sc cutoff bound i Λ h)

end Weight

end OddMath.QuiverHecke.ELVOld
