import OddMath.QuiverHecke.CyclotomicAction.ProbeGlobalDotInverse
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightDot
import Mathlib.CategoryTheory.Endomorphism

/-! # Invertible probe dots on weight-space induction
The global probe dot inverse is assembled on the prescribed weight-product
action, with zero objects at components without a predecessor. This supplies
the family-level dot input of InvertibleDotProbe.md Section 5, equation (6).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ)
  (ha : CyclotomicPolynomialParity D (probePolynomial (k := k) (probeDotExponent D) m))
local notation "a" => probePolynomial (k := k) (probeDotExponent D) m

section Weight
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The content dot between a block and its successor. -/
abbrev probeBlockDotInverse (β : WeightBlocks D Λ x) :=
  (probeGlobalContentDotIso D Sc i m ha (blockSucc_val D Λ i h β).symm).inv

/-- The dot component at a block with a chosen predecessor. -/
def probeGlobalWeightDotInverseVia (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (inductionComponent D Sc a ha i Λ h δ).obj M ⟶ (inductionComponent D Sc a ha i Λ h δ).obj M := by
  subst hβ
  exact eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M) ≫
    (probeBlockDotInverse D Sc m ha i Λ h β).app p (M β) ≫
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M).symm

theorem probeGlobalWeightDotInverseVia_eq (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x)
    (β β' : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ)
    (hβ' : blockSucc D Λ i h β' = δ) :
    probeGlobalWeightDotInverseVia D Sc m ha i Λ h p M β δ hβ =
      probeGlobalWeightDotInverseVia D Sc m ha i Λ h p M β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The dot component at a block: through the predecessor, or zero. -/
def probeGlobalWeightDotInverseComponent (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x)
    (δ : WeightBlocks D Λ y) :
    (inductionComponent D Sc a ha i Λ h δ).obj M ⟶ (inductionComponent D Sc a ha i Λ h δ).obj M :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    probeGlobalWeightDotInverseVia D Sc m ha i Λ h p M hδ.choose δ hδ.choose_spec
  else 0

theorem probeGlobalWeightDotInverseComponent_blockSucc (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x)
    (β : WeightBlocks D Λ x) :
    probeGlobalWeightDotInverseComponent D Sc m ha i Λ h p M (blockSucc D Λ i h β) =
      eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M) ≫
        (probeBlockDotInverse D Sc m ha i Λ h β).app p (M β) ≫
          eqToHom (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M).symm := by
  unfold probeGlobalWeightDotInverseComponent
  split
  · rename_i hc
    exact probeGlobalWeightDotInverseVia_eq D Sc m ha i Λ h p M _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem probeGlobalWeightDotInverseComponent_mem (p : ZMod 2) (M : WeightProduct D Sc a ha Λ x)
    (δ : WeightBlocks D Λ y) :
    probeGlobalWeightDotInverseComponent D Sc m ha i Λ h p M δ ∈ parity (R := k) _ _ p := by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    rw [probeGlobalWeightDotInverseComponent_blockSucc]
    have hm := comp_mem (eqToHom_mem_parity_zero
        (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M))
      (comp_mem ((probeBlockDotInverse D Sc m ha i Λ h β).app_mem p (M β))
        (eqToHom_mem_parity_zero (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M).symm))
    simpa only [zero_add, add_zero] using hm
  · rw [(inductionComponent_isZero D Sc a ha i Λ h δ hδ M).eq_of_src
      (probeGlobalWeightDotInverseComponent D Sc m ha i Λ h p M δ) 0]
    exact Submodule.zero_mem _

theorem probeGlobalWeightDotInverseComponent_naturality (p : ZMod 2) (β : WeightBlocks D Λ x)
    {M M' : WeightProduct D Sc a ha Λ x} {q : ZMod 2} (f : M ⟶ M')
    (hf : f ∈ parity (R := k) M M' q) :
    (inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).map f ≫
        probeGlobalWeightDotInverseComponent D Sc m ha i Λ h p M' (blockSucc D Λ i h β) =
      koszulSign p q • (probeGlobalWeightDotInverseComponent D Sc m ha i Λ h p M (blockSucc D Λ i h β) ≫
        (inductionComponent D Sc a ha i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [inductionComponent_map_blockSucc, probeGlobalWeightDotInverseComponent_blockSucc,
    probeGlobalWeightDotInverseComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hn := (probeBlockDotInverse D Sc m ha i Λ h β).naturality p (f β) (hf β)
  rw [← Category.assoc ((blockInd D Sc a ha i Λ h β).map (f β)), Superfunctor.map, hn,
    Linear.smul_comp, Linear.comp_smul, Category.assoc]

/-- **The dot on weight-space induction.** -/
def probeGlobalWeightDotInverse :
    SuperNatTrans k (globalEFunctor D Sc a ha i Λ h) (globalEFunctor D Sc a ha i Λ h) where
  app p M δ := probeGlobalWeightDotInverseComponent D Sc m ha i Λ h p M δ
  app_mem p M δ := probeGlobalWeightDotInverseComponent_mem D Sc m ha i Λ h p M δ
  naturality p M M' q f hf := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact probeGlobalWeightDotInverseComponent_naturality D Sc m ha i Λ h p β f hf
    · exact (inductionComponent_isZero D Sc a ha i Λ h δ hδ _).eq_of_src _ _


private theorem probe_transport_sum_one {C : Type*} [Category C] [Preadditive C]
    {A B : C} (hAB : A = B) (f₀ f₁ g₀ g₁ : End B)
    (hp : f₀ ≫ g₀ + f₁ ≫ g₁ = 𝟙 B) :
    (eqToHom hAB ≫ f₀ ≫ eqToHom hAB.symm) ≫ (eqToHom hAB ≫ g₀ ≫ eqToHom hAB.symm) +
      (eqToHom hAB ≫ f₁ ≫ eqToHom hAB.symm) ≫ (eqToHom hAB ≫ g₁ ≫ eqToHom hAB.symm) = 𝟙 A := by
  subst hAB
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hp

private theorem probe_transport_sum_zero {C : Type*} [Category C] [Preadditive C]
    {A B : C} (hAB : A = B) (f₀ f₁ g₀ g₁ : End B)
    (hp : f₀ ≫ g₀ + f₁ ≫ g₁ = 0) :
    (eqToHom hAB ≫ f₀ ≫ eqToHom hAB.symm) ≫ (eqToHom hAB ≫ g₀ ≫ eqToHom hAB.symm) +
      (eqToHom hAB ≫ f₁ ≫ eqToHom hAB.symm) ≫ (eqToHom hAB ≫ g₁ ≫ eqToHom hAB.symm) = 0 := by
  subst hAB
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hp

private theorem probe_weight_hom_inv_0 (M : WeightProduct D Sc a ha Λ x) :
    (SuperNatTrans.vcomp (globalWeightDot D Sc a ha i Λ h) (probeGlobalWeightDotInverse D Sc m ha i Λ h)).app 0 M =
      𝟙 ((globalEFunctor D Sc a ha i Λ h).obj M) := by
  funext δ
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change globalWeightDotComponent D Sc a ha i Λ h 0 M (blockSucc D Λ i h β) ≫ probeGlobalWeightDotInverseComponent D Sc m ha i Λ h 0 M (blockSucc D Λ i h β) +
          globalWeightDotComponent D Sc a ha i Λ h 1 M (blockSucc D Λ i h β) ≫ probeGlobalWeightDotInverseComponent D Sc m ha i Λ h 1 M (blockSucc D Λ i h β) = 𝟙 _
    rw [globalWeightDotComponent_blockSucc, globalWeightDotComponent_blockSucc,
      probeGlobalWeightDotInverseComponent_blockSucc,
      probeGlobalWeightDotInverseComponent_blockSucc]
    have hp : (blockDot D Sc a ha i Λ h β).app 0 (M β) ≫ (probeBlockDotInverse D Sc m ha i Λ h β).app 0 (M β) +
          (blockDot D Sc a ha i Λ h β).app 1 (M β) ≫ (probeBlockDotInverse D Sc m ha i Λ h β).app 1 (M β) = 𝟙 _ :=
      congrArg (fun η => η.app 0 (M β))
        (probeGlobalContentDotIso D Sc i m ha (blockSucc_val D Λ i h β).symm).hom_inv_id
    exact probe_transport_sum_one
      (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M) _ _ _ _ hp
  · exact (inductionComponent_isZero D Sc a ha i Λ h δ hδ M).eq_of_src _ _

private theorem probe_weight_hom_inv_1 (M : WeightProduct D Sc a ha Λ x) :
    (SuperNatTrans.vcomp (globalWeightDot D Sc a ha i Λ h) (probeGlobalWeightDotInverse D Sc m ha i Λ h)).app 1 M =
      0 := by
  funext δ
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change globalWeightDotComponent D Sc a ha i Λ h 0 M (blockSucc D Λ i h β) ≫ probeGlobalWeightDotInverseComponent D Sc m ha i Λ h 1 M (blockSucc D Λ i h β) +
          globalWeightDotComponent D Sc a ha i Λ h 1 M (blockSucc D Λ i h β) ≫ probeGlobalWeightDotInverseComponent D Sc m ha i Λ h 0 M (blockSucc D Λ i h β) = 0
    rw [globalWeightDotComponent_blockSucc, globalWeightDotComponent_blockSucc,
      probeGlobalWeightDotInverseComponent_blockSucc,
      probeGlobalWeightDotInverseComponent_blockSucc]
    have hp : (blockDot D Sc a ha i Λ h β).app 0 (M β) ≫ (probeBlockDotInverse D Sc m ha i Λ h β).app 1 (M β) +
          (blockDot D Sc a ha i Λ h β).app 1 (M β) ≫ (probeBlockDotInverse D Sc m ha i Λ h β).app 0 (M β) = 0 :=
      congrArg (fun η => η.app 1 (M β))
        (probeGlobalContentDotIso D Sc i m ha (blockSucc_val D Λ i h β).symm).hom_inv_id
    exact probe_transport_sum_zero
      (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M) _ _ _ _ hp
  · exact (inductionComponent_isZero D Sc a ha i Λ h δ hδ M).eq_of_src _ _

private theorem probe_weight_inv_hom_0 (M : WeightProduct D Sc a ha Λ x) :
    (SuperNatTrans.vcomp (probeGlobalWeightDotInverse D Sc m ha i Λ h) (globalWeightDot D Sc a ha i Λ h)).app 0 M =
      𝟙 ((globalEFunctor D Sc a ha i Λ h).obj M) := by
  funext δ
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change probeGlobalWeightDotInverseComponent D Sc m ha i Λ h 0 M (blockSucc D Λ i h β) ≫ globalWeightDotComponent D Sc a ha i Λ h 0 M (blockSucc D Λ i h β) +
          probeGlobalWeightDotInverseComponent D Sc m ha i Λ h 1 M (blockSucc D Λ i h β) ≫ globalWeightDotComponent D Sc a ha i Λ h 1 M (blockSucc D Λ i h β) = 𝟙 _
    rw [globalWeightDotComponent_blockSucc, globalWeightDotComponent_blockSucc,
      probeGlobalWeightDotInverseComponent_blockSucc,
      probeGlobalWeightDotInverseComponent_blockSucc]
    have hp : (probeBlockDotInverse D Sc m ha i Λ h β).app 0 (M β) ≫ (blockDot D Sc a ha i Λ h β).app 0 (M β) +
          (probeBlockDotInverse D Sc m ha i Λ h β).app 1 (M β) ≫ (blockDot D Sc a ha i Λ h β).app 1 (M β) = 𝟙 _ :=
      congrArg (fun η => η.app 0 (M β))
        (probeGlobalContentDotIso D Sc i m ha (blockSucc_val D Λ i h β).symm).inv_hom_id
    exact probe_transport_sum_one
      (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M) _ _ _ _ hp
  · exact (inductionComponent_isZero D Sc a ha i Λ h δ hδ M).eq_of_src _ _

private theorem probe_weight_inv_hom_1 (M : WeightProduct D Sc a ha Λ x) :
    (SuperNatTrans.vcomp (probeGlobalWeightDotInverse D Sc m ha i Λ h) (globalWeightDot D Sc a ha i Λ h)).app 1 M =
      0 := by
  funext δ
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change probeGlobalWeightDotInverseComponent D Sc m ha i Λ h 0 M (blockSucc D Λ i h β) ≫ globalWeightDotComponent D Sc a ha i Λ h 1 M (blockSucc D Λ i h β) +
          probeGlobalWeightDotInverseComponent D Sc m ha i Λ h 1 M (blockSucc D Λ i h β) ≫ globalWeightDotComponent D Sc a ha i Λ h 0 M (blockSucc D Λ i h β) = 0
    rw [globalWeightDotComponent_blockSucc, globalWeightDotComponent_blockSucc,
      probeGlobalWeightDotInverseComponent_blockSucc,
      probeGlobalWeightDotInverseComponent_blockSucc]
    have hp : (probeBlockDotInverse D Sc m ha i Λ h β).app 0 (M β) ≫ (blockDot D Sc a ha i Λ h β).app 1 (M β) +
          (probeBlockDotInverse D Sc m ha i Λ h β).app 1 (M β) ≫ (blockDot D Sc a ha i Λ h β).app 0 (M β) = 0 :=
      congrArg (fun η => η.app 1 (M β))
        (probeGlobalContentDotIso D Sc i m ha (blockSucc_val D Λ i h β).symm).inv_hom_id
    exact probe_transport_sum_zero
      (inductionComponent_obj_blockSucc D Sc a ha i Λ h β M) _ _ _ _ hp
  · exact (inductionComponent_isZero D Sc a ha i Λ h δ hδ M).eq_of_src _ _

/-- The prescribed dot is invertible on the original weight-product action. -/
def probeGlobalActionDotIso :
    globalActionE D Sc a ha i Λ h ≅ globalActionE D Sc a ha i Λ h where
  hom := globalActionDot D Sc a ha i Λ h
  inv := probeGlobalWeightDotInverse D Sc m ha i Λ h
  hom_inv_id := Superfunctor.hom_ext_parity
    (probe_weight_hom_inv_0 D Sc m ha i Λ h) (probe_weight_hom_inv_1 D Sc m ha i Λ h)
  inv_hom_id := Superfunctor.hom_ext_parity
    (probe_weight_inv_hom_0 D Sc m ha i Λ h) (probe_weight_inv_hom_1 D Sc m ha i Λ h)

/-- The inverse has the same colour parity, including for odd colours. -/
theorem probeGlobalActionDotIso_inv_mem :
    (probeGlobalActionDotIso D Sc m ha i Λ h).inv ∈
      parity (R := k) (globalActionE D Sc a ha i Λ h) (globalActionE D Sc a ha i Λ h)
        (D.parity i) :=
  inv_mem (probeGlobalActionDotIso D Sc m ha i Λ h) (globalActionDot_mem D Sc a ha i Λ h)

/-- The prescribed action dot is a unit in its endomorphism ring. -/
theorem probeGlobalActionDot_isUnit :
    IsUnit (End.of (globalActionDot D Sc a ha i Λ h)) := by
  apply (isUnit_iff_isIso _).2
  change IsIso (probeGlobalActionDotIso D Sc m ha i Λ h).hom
  infer_instance

end Weight
end OddMath.QuiverHecke.CyclotomicAction
