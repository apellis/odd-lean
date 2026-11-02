import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendTensors

/-! # Ordinary adjunction under weighted append comparison

DeformedActionAssembly §§5–6 and STATUS critical-chain item 2 require
compatibility of the chosen
old/truncated append comparison with the ordinary adjunction maps.
Restriction commutes with the actual quotient by an even comparison
whose components are identities. The selected append comparison
intertwines the literal counits after that restriction comparison.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "Q" => oldTruncateFunctor D Sc cutoff N
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "T" => truncatedAppend D Sc cutoff N [i]

/-- Pullback of truncated restriction and old restriction of pullback
are compared on the same module vector spaces. -/
def weightedAppendRestrictionIso :
    weightedRestriction D Sc cutoff N ((BalancedInduction.restriction T).obj M) ≅
      (BalancedInduction.restriction J).obj (weightedRestriction D Sc cutoff N M) :=
  moduleIsoOfEvenNatIso _ _
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun {v w} f => by
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      rw [Category.comp_id, Category.id_comp]
      obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
      rfl))
    (fun _ => id_mem _) (fun _ => id_mem _)

@[simp] theorem weightedAppendRestrictionIso_hom_app
    (p : ZMod 2) (s : OldCategory D Sc cutoff) :
    (weightedAppendRestrictionIso D Sc cutoff N i M).hom.app p s =
      if p = 0 then LinearMap.id else 0 := rfl

theorem weightedAppendRestrictionIso_hom_mem :
    (weightedAppendRestrictionIso D Sc cutoff N i M).hom ∈ parity (R := k) _ _ 0 := by
  unfold weightedAppendRestrictionIso
  exact moduleIsoOfEvenNatIso_hom_mem _ _ _ _ _

/-- The restriction comparison is natural for arbitrary supernatural
input-module maps, including their odd parts. -/
theorem weightedAppendRestrictionIso_naturality
    {L : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)} (f : M ⟶ L) :
    (BalancedInduction.restriction Q).map ((BalancedInduction.restriction T).map f) ≫
        (weightedAppendRestrictionIso D Sc cutoff N i L).hom =
      (weightedAppendRestrictionIso D Sc cutoff N i M).hom ≫
        (BalancedInduction.restriction J).map ((BalancedInduction.restriction Q).map f) := by
  apply Superfunctor.hom_ext
  intro p s
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [Superfunctor.comp_app, weightedAppendRestrictionIso_hom_app,
      BalancedInduction.restriction, Superfunctor.whiskerLeft_app,
      ↓reduceIte, zero_add, SVec.zmod2_one_add_one, one_ne_zero,
      LinearMap.id_comp, LinearMap.comp_id, LinearMap.zero_comp,
      LinearMap.comp_zero, add_zero, zero_add]

/-- The whole restriction square uses the same identity-vector
comparisons as the ordinary counit formula. -/
def weightedAppendRestrictionNaturalIso :
    BalancedInduction.restriction T ⋙ BalancedInduction.restriction Q ≅
      BalancedInduction.restriction Q ⋙ BalancedInduction.restriction J :=
  NatIso.ofComponents (weightedAppendRestrictionIso D Sc cutoff N i)
    (fun f => weightedAppendRestrictionIso_naturality D Sc cutoff N i _ f)

/-- The selected old/truncated append comparison carries the literal
ordinary counit to the truncated counit. The old-side source is identified
by the canonical even restriction-square comparison above. -/
theorem appendWeightedModuleIso_hom_counit (w : OldCategory D Sc cutoff) :
    BalancedInduction.counit T M.toFunctor ((Q).obj w) ∘ₗ
        (appendWeightedModuleIso D Sc cutoff N i
          ((BalancedInduction.restriction T).obj M)).hom.total ((Q).obj w) =
      BalancedInduction.counit J (weightedRestriction D Sc cutoff N M).toFunctor w ∘ₗ
        ((BalancedInduction.induction J).map
          (weightedAppendRestrictionIso D Sc cutoff N i M).hom).total w := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, appendWeightedModuleIso_hom_tensor,
    BalancedInduction.counit_tensor]
  have ht := BalancedInduction.moduleMap_total_tensor_even J
    (weightedAppendRestrictionIso D Sc cutoff N i M).hom
    (weightedAppendRestrictionIso_hom_mem D Sc cutoff N i M) w s g b
  have hb : (weightedAppendRestrictionIso D Sc cutoff N i M).hom.app 0 s b = b := rfl
  rw [hb] at ht
  rw [show ((BalancedInduction.induction J).map
      (weightedAppendRestrictionIso D Sc cutoff N i M).hom).total w
      (BalancedInduction.tensor J
        (weightedRestriction D Sc cutoff N ((BalancedInduction.restriction T).obj M)).toFunctor
        s g b) = _ from ht,
    BalancedInduction.counit_tensor]
  rfl

end OddMath.QuiverHecke.ELVOld
