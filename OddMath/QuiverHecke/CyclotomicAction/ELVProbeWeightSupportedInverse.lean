import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightAbsentInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightCapCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeAppendToLocalInverse

/-! # Local inverses on occupied OLD probe weight blocks

Brundan–Ellis (1.13)–(1.14): evaluate the prescribed stored-target
inverse and transport its principal, cap and unit entries through the
chosen global coordinates. Every inverse entry is retained.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₀)
local notation "δ" => blockSucc D Λ i h₁ β
local notation "ε" => blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)
local notation "ν" => Multiset.toList (Subtype.val β)
local notation "hl" => probeOldBlockTarget_perm D i Λ h₁ β (blockSucc D Λ i h₁ β) rfl
local notation "hu" => probeOldBlockTarget_perm D i Λ h₂ δ (blockSucc D Λ i h₂ δ) rfl
local notation "E₁" => probeOldE D Sc m i Λ h₁
local notation "F₁" => probeOldF D Sc m i Λ h₁
local notation "E₂" => probeOldE D Sc m i Λ h₂
local notation "F₂" => probeOldF D Sc m i Λ h₂
local notation "A₁" => probeOldActionAdjunction D Sc m i Λ h₁
local notation "A₂" => probeOldActionAdjunction D Sc m i Λ h₂
local notation "φ" => SKM.rouquierMate A₁ A₂
  (probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂)
local notation "UnitField" n => SKM.SuperAdjunction.unit (probeOldActionAdjunction D Sc m i Λ h₂) ≫ SKM.rouquierPower (probeOldActionDot D Sc m i Λ h₂) n ▷ F₂
local notation "CapField" n => F₁ ◁ SKM.rouquierPower (probeOldActionDot D Sc m i Λ h₁) n ≫ SKM.SuperAdjunction.counit (probeOldActionAdjunction D Sc m i Λ h₁)
local notation "C" => ProbeCanonicalModules D Sc m (Subtype.val δ)
local notation "ψ" => probeAppendToMate D Sc m ν i hl hu

private theorem source_obj (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    ((F₁ ≫ E₁).obj M) δ =
      (probeEvaluatedAppendTo D Sc m ν i δ.1.toList hl).obj
        ((probeEvaluatedRestrictTo D Sc m ν i δ.1.toList hl).obj (M δ)) :=
  probeOldWeightMixedSource_obj D Sc m i i Λ h₁ h₁ β M

private theorem target_obj (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    ((E₂ ≫ F₂).obj M) δ =
      (probeEvaluatedRestrictTo D Sc m δ.1.toList i ε.1.toList hu).obj
        ((probeEvaluatedAppendTo D Sc m δ.1.toList i ε.1.toList hu).obj (M δ)) :=
  probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M

include h₁ in
private theorem stored_height (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) :
    -contentCrossingHeight D (probeCutoff D m) i ((i :: ν : List I) : Multiset I) = D.h i x₁ := by
  have hc := Multiset.coe_eq_coe.mpr hl
  rw [Multiset.coe_toList] at hc
  rw [hc, contentCrossingHeight_eq_neg_weight D (probeCutoff D m) i Λ x₁ hcutoff δ, neg_neg]

/-- The occupied nonpositive-height coordinate has the specified unit inverse. -/
theorem probeOldWeightSupportedUnitInverse_nonempty
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) (hh : D.h i x₁ ≤ 0)
    (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (UnitField n).total M δ) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (-D.h i x₁).toNat) := by
  have hHeight := stored_height D m i Λ h₁ β hcutoff
  have hneg : -contentCrossingHeight D (probeCutoff D m) i ((i :: ν : List I) : Multiset I) ≤ 0 := by
    simpa only [hHeight] using hh
  let J := (probeAppendToInvNeg D Sc m ν i hl hu hneg).at (M δ)
  let a := eqToIso (target_obj D Sc m i Λ h₁ h₂ β M)
  let b := eqToIso (source_obj D Sc m i Λ h₁ β M)
  let c := Iso.refl (M δ)
  have hc : c.hom = 𝟙 (M δ) := rfl
  have H := J.mapCoordinates (𝟭 C) a b c
    (eqToHom_mem_parity_zero (target_obj D Sc m i Λ h₁ h₂ β M))
    (eqToHom_mem_parity_zero (source_obj D Sc m i Λ h₁ β M)) (id_mem _)
  have hf : b.hom ≫ (𝟭 C).map ((ψ).app (D.parity i) (M δ)) ≫ a.inv =
      (φ).app (D.parity i) M δ := by
    have hs : (φ).app (D.parity i) M δ ≫ a.hom = b.hom ≫ (ψ).app (D.parity i) (M δ) :=
      probeOldWeightRouquierMate_comparison D Sc m i Λ h₁ h₂ β (D.parity i) M
    simpa only [Functor.id_map, ← Category.assoc] using (Iso.comp_inv_eq a).2 hs.symm
  have ha : a.hom = (probeOldBlockRes D Sc m i Λ h₂ δ).map
      (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)) :=
    (eqToHom_map (probeOldBlockRes D Sc m i Λ h₂ δ).toFunctor
      (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)).symm
  have hg (n : ℕ) : c.hom ≫ (𝟭 C).map
      ((probeAppendToUnitColumn D Sc m δ.1.toList i hu n).total (M δ)) ≫ a.inv = (UnitField n).total M δ := by
    have hs : (UnitField n).total M δ ≫ a.hom = c.hom ≫
        (probeAppendToUnitColumn D Sc m δ.1.toList i hu n).total (M δ) := by
      simpa only [ha, hc, Category.id_comp] using
        probeOldWeightUnitPower_total_comparison D Sc m i Λ h₂ δ M n
    simpa only [Functor.id_map, ← Category.assoc] using (Iso.comp_inv_eq a).2 hs.symm
  let H' := H.copyMaps ((φ).app (D.parity i) M δ) (fun n => (UnitField n).total M δ)
    hf.symm (funext fun n => (hg n).symm)
  exact ⟨by simpa only [hHeight] using H'⟩

/-- The occupied nonnegative-height coordinate has the specified cap inverse. -/
theorem probeOldWeightSupportedCapInverse_nonempty
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ) (hh : 0 ≤ D.h i x₁)
    (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (CapField n).total M δ) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (D.h i x₁).toNat) := by
  have hHeight := stored_height D m i Λ h₁ β hcutoff
  have hpos : 0 ≤ -contentCrossingHeight D (probeCutoff D m) i ((i :: ν : List I) : Multiset I) := by
    simpa only [hHeight] using hh
  let J := (probeAppendToInvPos D Sc m ν i hl hu hpos).at (M δ)
  let a := eqToIso (source_obj D Sc m i Λ h₁ β M)
  let b := eqToIso (target_obj D Sc m i Λ h₁ h₂ β M)
  let c := Iso.refl (M δ)
  have H := J.mapCoordinates (𝟭 C) a b c
    (eqToHom_mem_parity_zero (source_obj D Sc m i Λ h₁ β M))
    (eqToHom_mem_parity_zero (target_obj D Sc m i Λ h₁ h₂ β M)) (id_mem _)
  have hf : a.hom ≫ (𝟭 C).map ((ψ).app (D.parity i) (M δ)) ≫ b.inv =
      (φ).app (D.parity i) M δ := by
    have hs : (φ).app (D.parity i) M δ ≫ b.hom = a.hom ≫ (ψ).app (D.parity i) (M δ) :=
      probeOldWeightRouquierMate_comparison D Sc m i Λ h₁ h₂ β (D.parity i) M
    simpa only [Functor.id_map, ← Category.assoc] using (Iso.comp_inv_eq b).2 hs.symm
  have hg (n : ℕ) : a.hom ≫ (𝟭 C).map
      ((probeAppendToCapRow D Sc m ν i hl n).total (M δ)) ≫ c.inv = (CapField n).total M δ := by
    let r : (probeEvaluatedAppendTo D Sc m ν i δ.1.toList hl).obj
        ((probeEvaluatedRestrictTo D Sc m ν i δ.1.toList hl).obj (M δ)) ⟶ M δ :=
      (probeAppendToCapRow D Sc m ν i hl n).total (M δ)
    change a.hom ≫ r ≫ 𝟙 (M δ) = _
    rw [Category.comp_id]
    exact (probeOldWeightCapPower_total_comparison D Sc m i Λ h₁ β M n).symm
  let H' := H.copyMaps ((φ).app (D.parity i) M δ) (fun n => (CapField n).total M δ)
    hf.symm (funext fun n => (hg n).symm)
  exact ⟨by simpa only [hHeight] using H'⟩

end OddMath.QuiverHecke
