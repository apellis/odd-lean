/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightModules
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToDotUnit

/-! # The prescribed signed dot on the global OLD probe

`SwappedActionAssembly` F2: the actual old append dot acts on every
original-weight block. Its only nonzero parity component is the moving
colour parity. Absent predecessors contribute the zero module. No
invertibility statement is made for arbitrary unevaluated old modules.
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

/-- The exact chosen stored-target OLD dot, without a comparison isomorphism. -/
abbrev probeOldBlockDot (β : WeightBlocks D Λ x) :=
  probeAppendToInductionDot D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList
    (by
      apply Multiset.coe_eq_coe.mp
      rw [Multiset.coe_toList]
      change {i} + (β.1.toList : Multiset I) = (blockSucc D Λ i h β).1
      rw [Multiset.coe_toList, blockSucc_val])

theorem probeOldBlockDot_mem (β : WeightBlocks D Λ x) :
    probeOldBlockDot D Sc m i Λ h β ∈ parity (R := k)
      (probeOldBlockInd D Sc m i Λ h β) (probeOldBlockInd D Sc m i Λ h β) (D.parity i) :=
  probeAppendToInductionDot_mem D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList _

theorem probeOldBlockDot_homogeneous (β : WeightBlocks D Λ x) :
    (probeOldBlockDot D Sc m i Λ h β).IsHomogeneous (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.1 (probeOldBlockDot_mem D Sc m i Λ h β)

/-- The dot component at a block with a chosen predecessor. -/
def probeOldWeightDotVia (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj M ⟶ (probeOldInductionComponent D Sc m i Λ h δ).obj M := by
  subst hβ
  exact eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M) ≫
    (probeOldBlockDot D Sc m i Λ h β).app p (M β) ≫
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm

theorem probeOldWeightDotVia_eq (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x)
    (β β' : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ)
    (hβ' : blockSucc D Λ i h β' = δ) :
    probeOldWeightDotVia D Sc m i Λ h p M β δ hβ =
      probeOldWeightDotVia D Sc m i Λ h p M β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The dot component at a block: through the predecessor, or zero. -/
def probeOldWeightDotComponent (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x)
    (δ : WeightBlocks D Λ y) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj M ⟶ (probeOldInductionComponent D Sc m i Λ h δ).obj M :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    probeOldWeightDotVia D Sc m i Λ h p M hδ.choose δ hδ.choose_spec
  else 0

theorem probeOldWeightDotComponent_blockSucc (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x)
    (β : WeightBlocks D Λ x) :
    probeOldWeightDotComponent D Sc m i Λ h p M (blockSucc D Λ i h β) =
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M) ≫
        (probeOldBlockDot D Sc m i Λ h β).app p (M β) ≫
          eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm := by
  unfold probeOldWeightDotComponent
  split
  · rename_i hc
    exact probeOldWeightDotVia_eq D Sc m i Λ h p M _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem probeOldWeightDotComponent_mem (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x)
    (δ : WeightBlocks D Λ y) :
    probeOldWeightDotComponent D Sc m i Λ h p M δ ∈ parity (R := k) _ _ p := by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    rw [probeOldWeightDotComponent_blockSucc]
    have hm := comp_mem (eqToHom_mem_parity_zero
        (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M))
      (comp_mem ((probeOldBlockDot D Sc m i Λ h β).app_mem p (M β))
        (eqToHom_mem_parity_zero (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm))
    simpa only [zero_add, add_zero] using hm
  · rw [(probeOldInductionComponent_isZero D Sc m i Λ h δ hδ M).eq_of_src
      (probeOldWeightDotComponent D Sc m i Λ h p M δ) 0]
    exact Submodule.zero_mem _

theorem probeOldWeightDotComponent_naturality (p : ZMod 2) (β : WeightBlocks D Λ x)
    {M M' : ProbeOldWeightProduct D Sc m Λ x} {q : ZMod 2} (f : M ⟶ M')
    (hf : f ∈ parity (R := k) M M' q) :
    (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map f ≫
        probeOldWeightDotComponent D Sc m i Λ h p M' (blockSucc D Λ i h β) =
      koszulSign p q • (probeOldWeightDotComponent D Sc m i Λ h p M (blockSucc D Λ i h β) ≫
        (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [probeOldInductionComponent_map_blockSucc, probeOldWeightDotComponent_blockSucc,
    probeOldWeightDotComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hn := (probeOldBlockDot D Sc m i Λ h β).naturality p (f β) (hf β)
  rw [← Category.assoc ((probeOldBlockInd D Sc m i Λ h β).map (f β)), Superfunctor.map, hn,
    Linear.smul_comp, Linear.comp_smul, Category.assoc]

/-- **The dot on weight-space induction.** -/
def probeOldWeightDot :
    SuperNatTrans k (probeOldEFunctor D Sc m i Λ h) (probeOldEFunctor D Sc m i Λ h) where
  app p M δ := probeOldWeightDotComponent D Sc m i Λ h p M δ
  app_mem p M δ := probeOldWeightDotComponent_mem D Sc m i Λ h p M δ
  naturality p M M' q f hf := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact probeOldWeightDotComponent_naturality D Sc m i Λ h p β f hf
    · exact (probeOldInductionComponent_isZero D Sc m i Λ h δ hδ _).eq_of_src _ _

/-- Only the component of the colour parity is nonzero. -/
theorem probeOldWeightDot_homogeneous :
    (probeOldWeightDot D Sc m i Λ h).IsHomogeneous (D.parity i) := by
  intro q hq
  funext M
  funext δ
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change probeOldWeightDotComponent D Sc m i Λ h q M (blockSucc D Λ i h β) = 0
    rw [probeOldWeightDotComponent_blockSucc,
      congrFun (probeOldBlockDot_homogeneous D Sc m i Λ h β q hq)
        (M β)]
    simp
  · exact (probeOldInductionComponent_isZero D Sc m i Λ h δ hδ M).eq_of_src _ _

/-- The dot as a 2-endomorphism of weight-space induction in the action target. -/
def probeOldActionDot : probeOldE D Sc m i Λ h ⟶ probeOldE D Sc m i Λ h :=
  probeOldWeightDot D Sc m i Λ h

/-- The dot has the parity of its colour, including for odd colours. -/
theorem probeOldActionDot_mem :
    probeOldActionDot D Sc m i Λ h ∈
      parity (R := k) (probeOldE D Sc m i Λ h) (probeOldE D Sc m i Λ h)
        (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.2 (probeOldWeightDot_homogeneous D Sc m i Λ h)

end OddMath.QuiverHecke
