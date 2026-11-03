import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightLocalMateCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightUnitCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMissingStoredLocal
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightMatrixHeight
import OddMath.SKM.AugmentedInverseEvaluation

/-! # Local inverses at missing probe weight predecessors

Brundan–Ellis (1.13)–(1.14): the missing-colour stored local record supplies
both prescribed global inverse presentations. The lower mixed coordinate
is the constructed zero object; the upper unit columns retain their
selected successor chart. The cutoff matches the categorical weight.
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
local notation "E₁" => probeOldE D Sc m i Λ h₁
local notation "F₁" => probeOldF D Sc m i Λ h₁
local notation "E₂" => probeOldE D Sc m i Λ h₂
local notation "F₂" => probeOldF D Sc m i Λ h₂
local notation "A₁" => probeOldActionAdjunction D Sc m i Λ h₁
local notation "A₂" => probeOldActionAdjunction D Sc m i Λ h₂
local notation "φ" => SKM.rouquierMate A₁ A₂
  (probeOldActionCross D Sc m Λ i i h₁ h₂ h₁ h₂)
local notation "U" n => (A₂).unit ≫ SKM.rouquierPower (probeOldActionDot D Sc m i Λ h₂) n ▷ F₂
local notation "R" n => F₁ ◁ SKM.rouquierPower (probeOldActionDot D Sc m i Λ h₁) n ≫ (A₁).counit
variable (δ : WeightBlocks D Λ x₁)
local notation "ε" => blockSucc D Λ i h₂ δ
local notation "γ" => Multiset.toList (Subtype.val δ)
local notation "μ" => Multiset.toList (Subtype.val ε)
local notation "perm" => probeOldBlockTarget_perm D i Λ h₂ δ (blockSucc D Λ i h₂ δ) rfl
local notation "Z" => probeEvaluatedZeroCell D Sc m γ
local notation "B₀" => probeEvaluatedZeroAdjunction D Sc m γ
local notation "e" => probeAppendToE D Sc m γ i μ perm
local notation "f" => probeAppendToF D Sc m γ i μ perm
local notation "B₁" => probeAppendToRightAdjunction D Sc m γ i μ perm
local notation "ψ" => SKM.rouquierMate B₀ B₁ (0 : End (Z ≫ e))
local notation "C" => ProbeEvaluatedModules D Sc m γ

/-- The following induction always uses its specified successor block. -/
theorem probeOldWeightFollowing_obj (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    ((E₂ ≫ F₂).obj M) δ = (e ≫ f).obj (M δ) := by
  change (probeOldBlockRes D Sc m i Λ h₂ δ).obj
    ((probeOldInductionComponent D Sc m i Λ h₂ ε).obj M) = _
  exact congrArg (fun N => (probeOldBlockRes D Sc m i Λ h₂ δ).obj N)
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)

/-- The chosen upper-loop coordinate equality keeps its even map explicitly. -/
theorem probeOldWeightFollowing_eqToHom (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M) =
      (probeOldBlockRes D Sc m i Λ h₂ δ).map
        (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)) :=
  (eqToHom_map (probeOldBlockRes D Sc m i Λ h₂ δ).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₂ δ M)).symm

/-- Every missing predecessor has the specified unit inverse, including height zero. -/
theorem probeOldWeightAbsentUnitInverse_nonempty
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ)
    (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (U n).total M δ) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (-D.h i x₁).toNat) := by
  have hi : i ∉ δ.1 := fun hm => hδ ((exists_blockSucc_iff D Λ i h₁ δ).mpr hm)
  have hil : i ∉ γ := by simpa only [Multiset.mem_toList] using hi
  have hHeight : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) = D.h i x₁ := by
    rw [Multiset.coe_toList, contentCrossingHeight_eq_neg_weight D (probeCutoff D m) i Λ x₁ hcutoff δ, neg_neg]
  have hh : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) ≤ 0 :=
    neg_nonpos.mpr (contentCrossingHeight_nonneg_of_not_mem D (probeCutoff D m) γ i hil)
  let J := ((probeMissingStoredLoc D Sc m γ i perm hil).invNeg hh).at (M δ)
  let a := eqToIso (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M)
  have hB : Limits.IsZero (((F₁ ≫ E₁).obj M) δ) :=
    probeOldInductionComponent_isZero D Sc m i Λ h₁ δ hδ ((F₁).obj M)
  have hZ : Limits.IsZero ((Z ≫ Z).obj (M δ)) := probeEvaluatedZeroModule_isZero D Sc m γ
  let b := hB.iso hZ
  let c := Iso.refl (M δ)
  have hc : c.hom = 𝟙 (M δ) := rfl
  have hb : b.hom ∈ parity (R := k) _ _ 0 := by
    rw [hB.eq_of_src b.hom 0]
    exact Submodule.zero_mem _
  have H := J.mapCoordinates (𝟭 C) a b c
    (eqToHom_mem_parity_zero (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M)) hb (id_mem _)
  have hf : b.hom ≫ (𝟭 C).map ((ψ).app (D.parity i) (M δ)) ≫ a.inv =
      (φ).app (D.parity i) M δ := hB.eq_of_src _ _
  have hg (n : ℕ) : c.hom ≫ (𝟭 C).map
      ((probeAppendToUnitColumn D Sc m γ i perm n).total (M δ)) ≫ a.inv = (U n).total M δ := by
    have hs : (U n).total M δ ≫ a.hom = c.hom ≫
        (probeAppendToUnitColumn D Sc m γ i perm n).total (M δ) := by
      simpa only [a, eqToIso.hom, hc, Category.id_comp,
        probeOldWeightFollowing_eqToHom] using
        probeOldWeightUnitPower_total_comparison D Sc m i Λ h₂ δ M n
    simpa only [Functor.id_map, ← Category.assoc] using (Iso.comp_inv_eq a).2 hs.symm
  exact ⟨by simpa only [hHeight, hf, hg] using H⟩

/-- The same missing-colour record supplies the cap orientation at height zero. -/
theorem probeOldWeightAbsentCapInverse_nonempty
    (hcutoff : (probeCutoff D m i : ℤ) = D.h i Λ)
    (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ) (hh : 0 ≤ D.h i x₁)
    (M : ProbeOldWeightProduct D Sc m Λ x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (R n).total M δ) (D.parity i)
      (fun n => (n : ZMod 2) * D.parity i) (D.h i x₁).toNat) := by
  have hi : i ∉ δ.1 := fun hm => hδ ((exists_blockSucc_iff D Λ i h₁ δ).mpr hm)
  have hil : i ∉ γ := by simpa only [Multiset.mem_toList] using hi
  have hHeight : -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) = D.h i x₁ := by
    rw [Multiset.coe_toList, contentCrossingHeight_eq_neg_weight D (probeCutoff D m) i Λ x₁ hcutoff δ, neg_neg]
  have hpos : 0 ≤ -contentCrossingHeight D (probeCutoff D m) i (γ : Multiset I) := by
    simpa only [hHeight] using hh
  let J := ((probeMissingStoredLoc D Sc m γ i perm hil).invPos hpos).at (M δ)
  let a := eqToIso (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M)
  have hB : Limits.IsZero (((F₁ ≫ E₁).obj M) δ) :=
    probeOldInductionComponent_isZero D Sc m i Λ h₁ δ hδ ((F₁).obj M)
  have hZ : Limits.IsZero ((Z ≫ Z).obj (M δ)) := probeEvaluatedZeroModule_isZero D Sc m γ
  let b := hB.iso hZ
  let c := Iso.refl (M δ)
  have hb : b.hom ∈ parity (R := k) _ _ 0 := by
    rw [hB.eq_of_src b.hom 0]
    exact Submodule.zero_mem _
  have H := J.mapCoordinates (𝟭 C) b a c hb
    (eqToHom_mem_parity_zero (probeOldWeightFollowing_obj D Sc m i Λ h₂ δ M)) (id_mem _)
  have hf : b.hom ≫ (𝟭 C).map ((ψ).app (D.parity i) (M δ)) ≫ a.inv =
      (φ).app (D.parity i) M δ := hB.eq_of_src _ _
  have hg (n : ℕ) : b.hom ≫ (𝟭 C).map
      ((Z ◁ SKM.rouquierPower (0 : End Z) n ≫ (B₀).counit).total (M δ)) ≫ c.inv =
      (R n).total M δ := hB.eq_of_src _ _
  exact ⟨by simpa only [hHeight, hf, hg] using H⟩

end OddMath.QuiverHecke
