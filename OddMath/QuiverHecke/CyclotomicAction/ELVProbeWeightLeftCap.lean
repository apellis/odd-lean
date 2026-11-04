import OddMath.QuiverHecke.CyclotomicAction.ELVProbeRouquierFamily
import OddMath.SKM.RouquierInverseRelations

/-! # The whole-weight probe left cap at a missing predecessor

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
compare the inverse-defined whole-weight cap with the stored local cap
using their actual unit columns. Inverse uniqueness removes dependence
on the choices used to assemble the whole-weight inverse family.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction ELVOld.CyclotomicCrossingTensor CyclotomicAction
universe u v w
private theorem cap_window_total
    {k : Type u} {C : Type v} [CommRing k] [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F : Superfunctor k C C}
    (a : Superfunctor.id k C ⟶ F) (b : F ⟶ Superfunctor.id k C)
    (q : Prop) [Decidable q]
    (h : a ≫ b = if q then 𝟙 (Superfunctor.id k C) else 0) (M : C) :
    a.total M ≫ b.total M = if q then 𝟙 M else 0 := by
  have hh := congrArg (fun η : Superfunctor.id k C ⟶ Superfunctor.id k C => η.total M) h
  rw [Superfunctor.comp_total] at hh
  by_cases hq : q
  · rw [ite_eq_left hq] at hh ⊢
    exact hh.trans (SuperNatTrans.id_total (𝟭 C) M)
  · rw [ite_eq_right hq] at hh ⊢
    simpa only [SuperNatTrans.total, Superfunctor.zero_app, zero_add] using hh

private theorem product_window {ι : Type*} {C : ι → Type*}
    [∀ j, Category (C j)] [∀ j, Preadditive (C j)]
    {A B : ∀ j, C j} (f : A ⟶ B) (g : B ⟶ A) (q : Prop) [Decidable q]
    (h : f ≫ g = if q then 𝟙 A else 0) (j : ι) :
    f j ≫ g j = if q then 𝟙 (A j) else 0 := by
  by_cases hq : q
  · rw [ite_eq_left hq] at h ⊢
    exact congrFun h j
  · rw [ite_eq_right hq] at h ⊢
    exact congrFun h j

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (δ : WeightBlocks D Λ x₁)
local notation "γ" => Multiset.toList (Subtype.val δ)
local notation "perm" => probeOldBlockTarget_perm D i Λ h₂ δ (blockSucc D Λ i h₂ δ) rfl
local notation "L" hc => probeOldWeightLoc D Sc m i Λ h₁ h₂ hc
local notation "U" n => SKM.SuperAdjunction.unit (probeOldActionAdjunction D Sc m i Λ h₂) ≫
  SKM.rouquierPower (probeOldActionDot D Sc m i Λ h₂) n ▷ probeOldF D Sc m i Λ h₂

/-- At a negative-height missing predecessor, the whole-weight raw cap
is exactly the stored missing-colour cap in its prescribed successor
chart. All input modules and all homogeneous components are retained. -/
theorem probeOldWeightLoc_cap_missing
    (hc : (probeCutoff D m i : ℤ) = D.h i Λ)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ)
    (hh : D.h i x₁ < 0) (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    ((L hc).capL).total M δ =
      eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M) ≫
        (probeMissingStoredLoc D Sc m γ i perm
          (by simpa only [Multiset.mem_toList] using
            (show i ∉ δ.1 from fun hm => hδ ((exists_blockSucc_iff D Λ i h₁ δ).mpr hm)))).capL.total (M δ) := by
  have hi : i ∉ γ := by
    simpa only [Multiset.mem_toList] using
      (show i ∉ δ.1 from fun hm => hδ ((exists_blockSucc_iff D Λ i h₁ δ).mpr hm))
  let S := probeMissingStoredLoc D Sc m γ i perm hi
  have hHeight : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) = D.h i x₁ := by
    rw [Multiset.coe_toList, contentCrossingHeight_eq_neg_weight D (probeCutoff D m) i Λ x₁ hc δ, neg_neg]
  have hs : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) < 0 := by
    simpa only [hHeight] using hh
  let J := Classical.choice (probeOldWeightAbsentUnitInverse_nonempty D Sc m i Λ h₁ h₂ δ hc hδ M)
  apply J.hom_ext
  · exact (probeOldInductionComponent_isZero D Sc m i Λ h₁ δ hδ
      ((probeOldF D Sc m i Λ h₁).obj M)).eq_of_src _ _
  · intro n hn
    have hL := cap_window_total ((L hc).cupD n) (L hc).capL _
      ((L hc).cupD_capL hh hn) M
    have hLc := product_window _ _ _ hL δ
    have hS := cap_window_total (S.cupD n) S.capL _
      (S.cupD_capL hs (by simpa only [hHeight] using hn)) (M δ)
    have hcol := probeOldWeightUnitPower_total_comparison D Sc m i Λ h₂ δ M n
    rw [← probeOldWeightFollowing_eqToHom] at hcol
    change (U n).total M δ ≫ eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M) =
      (S.cupD n).total (M δ) at hcol
    change (U n).total M δ ≫ (L hc).capL.total M δ = _
    calc
      _ = if n = (-D.h i x₁ - 1).toNat then 𝟙 (M δ) else 0 := by
        exact hLc
      _ = (S.cupD n).total (M δ) ≫ S.capL.total (M δ) := by
        simpa only [hHeight] using hS.symm
      _ = (U n).total M δ ≫
          (eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M) ≫ S.capL.total (M δ)) := by
        rw [← hcol, Category.assoc]

end OddMath.QuiverHecke
