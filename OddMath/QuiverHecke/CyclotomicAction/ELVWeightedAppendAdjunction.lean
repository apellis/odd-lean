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
section CounitCarriers
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (M : Superfunctor k D (SVec k))

/-- The ordinary counit on the literal coend of the restricted module. -/
def restrictionCounitLinear (w : D) :
    BalancedInduction.Obj J ((BalancedInduction.restriction J).obj M).toFunctor w →ₗ[k] M.obj w :=
  BalancedInduction.counit J M.toFunctor w

/-- This carrier realization is the prescribed ordinary counit. -/
theorem restrictionCounitLinear_apply (w : D)
    (b : BalancedInduction.Obj J ((BalancedInduction.restriction J).obj M).toFunctor w) :
    restrictionCounitLinear J M w b = BalancedInduction.counit J M.toFunctor w b := rfl

/-- The canonical counit evaluates its exact tensor arrow. -/
theorem restrictionCounitLinear_tensor (v : C) (w : D) (g : J.obj v ⟶ w)
    (b : M.obj (J.obj v)) :
    restrictionCounitLinear J M w
      (BalancedInduction.tensor J ((BalancedInduction.restriction J).obj M).toFunctor v g b) =
      M.map g b :=
  BalancedInduction.counit_tensor J M.toFunctor w v g b
end CounitCarriers

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
  let v : TruncatedCategory D Sc cutoff N := ⟨s.word ++ [i]⟩
  rcases parity_eq_zero_or_one p with rfl | rfl
  · change (LinearMap.id : L.obj v →ₗ[k] L.obj v) ∘ₗ f.app 0 v +
        (0 : L.obj v →ₗ[k] L.obj v) ∘ₗ f.app 1 v =
      f.app 0 v ∘ₗ (LinearMap.id : M.obj v →ₗ[k] M.obj v) +
        f.app 1 v ∘ₗ (0 : M.obj v →ₗ[k] M.obj v)
    simp only [LinearMap.id_comp, LinearMap.zero_comp, LinearMap.comp_id,
      LinearMap.comp_zero, add_zero]
  · change (0 : L.obj v →ₗ[k] L.obj v) ∘ₗ f.app 0 v +
        (LinearMap.id : L.obj v →ₗ[k] L.obj v) ∘ₗ f.app 1 v =
      f.app 1 v ∘ₗ (LinearMap.id : M.obj v →ₗ[k] M.obj v) +
        f.app 0 v ∘ₗ (0 : M.obj v →ₗ[k] M.obj v)
    simp only [LinearMap.zero_comp, LinearMap.id_comp, LinearMap.comp_id,
      LinearMap.comp_zero, zero_add, add_zero]

/-- The whole restriction square uses the same identity-vector
comparisons as the ordinary counit formula. -/
def weightedAppendRestrictionNaturalIso :
    BalancedInduction.restriction (k := k) T ⋙ BalancedInduction.restriction (k := k) Q ≅
      BalancedInduction.restriction (k := k) Q ⋙ BalancedInduction.restriction (k := k) J :=
  NatIso.ofComponents (weightedAppendRestrictionIso D Sc cutoff N i)
    (fun f => weightedAppendRestrictionIso_naturality D Sc cutoff N i _ f)

/-- The selected old/truncated append comparison carries the literal
ordinary counit to the truncated counit. The old-side source is identified
by the canonical even restriction-square comparison above. -/
theorem appendWeightedModuleIso_hom_counit (w : OldCategory D Sc cutoff) :
    restrictionCounitLinear T M ((Q).obj w) ∘ₗ
        weightedAppendComparisonLinear D Sc cutoff N i
          ((BalancedInduction.restriction T).obj M) w =
      restrictionCounitLinear J (weightedRestriction D Sc cutoff N M) w ∘ₗ
        BalancedInduction.mapComponent J
          (weightedAppendRestrictionIso D Sc cutoff N i M).hom 0 w := by
  apply BalancedInduction.hom_ext
  intro s g b
  let A := weightedRestriction D Sc cutoff N ((BalancedInduction.restriction T).obj M)
  let B := (BalancedInduction.restriction J).obj (weightedRestriction D Sc cutoff N M)
  let e := weightedAppendRestrictionIso D Sc cutoff N i M
  have ht := appendWeightedModuleIso_hom_tensor D Sc cutoff N i
    ((BalancedInduction.restriction T).obj M) s w g b
  have hT := restrictionCounitLinear_tensor T M ((Q).obj s) ((Q).obj w) ((Q).map g) b
  have hm := BalancedInduction.mapComponent_tensor J e.hom 0 w s g b
  have hb : e.hom.app 0 s b = b := rfl
  have hx : BalancedInduction.mapComponent J e.hom 0 w
      (BalancedInduction.tensor J A.toFunctor s g b) =
      BalancedInduction.tensor J B.toFunctor s g b := by
    refine hm.trans ?_
    exact congrArg₂ (fun z x => BalancedInduction.tensor J B.toFunctor s z x)
      (twist_zero g) hb
  have hJ := restrictionCounitLinear_tensor J (weightedRestriction D Sc cutoff N M) s w g b
  have hleft := (congrArg (restrictionCounitLinear T M ((Q).obj w)) ht).trans hT
  have hright :=
    (congrArg (restrictionCounitLinear J (weightedRestriction D Sc cutoff N M) w) hx).trans hJ
  exact hleft.trans hright.symm

end OddMath.QuiverHecke.ELVOld
