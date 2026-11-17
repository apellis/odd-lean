import Mathlib.CategoryTheory.Conj
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightCap.ProbeCapUniqueness
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightQuadratic.ProbeAppendToMateReindex

/-!
# Probe weight cap

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
open ELV ELV.BalancedInduction ELV.CyclotomicCrossingTensor CyclotomicAction
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
end

end

section

/-! # Negative-height normalization of the whole-weight probe counit

SwappedActionAssembly F2: retain the prescribed diagonal Koszul factor
of the whole-weight left adjunction. Multiplying its normalized counit
by that factor recovers the exact raw inverse cap. On missing blocks,
the cap is then the previously identified stored local row.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
universe u
private theorem total_zsmul
    {k C A : Type*} [CommRing k] [Category C] [Category A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : Superfunctor k C A} (η : F ⟶ G) (z : ℤ) (M : C) :
    (z • η).total M = z • η.total M := by
  change z • η.app 0 M + z • η.app 1 M = z • (η.app 0 M + η.app 1 M)
  exact (smul_add _ _ _).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (Λ : X)
  (hc : ∀ i, (probeCutoff D m i : ℤ) = D.h i Λ)
local notation "T" => probeOldRouquierFamily D Sc m Λ hc

/-- The diagonal parity factor exactly cancels the prescribed
negative-height normalization of the whole-weight left counit. -/
theorem probeOldLeftCounit_negative_sign (i : I) {x y : X}
    (h : x + D.α i = y) (hh : D.h i x < 0) :
    koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x) • ((T).leftAdjoints.adjL i h).counit =
      (probeOldWeightLoc D Sc m i Λ (sub_add_cancel x (D.α i)) h (hc i)).capL := by
  change koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x) • ((T).leftAdjoints.adjL i h).counit = (T).leftCap i h
  rw [SKM.RouquierFamily.leftAdjoints_counit, SKM.RouquierFamily.leftAdjScalar_inv_coe,
    ite_eq_left hh, mul_one, Int.cast_smul_eq_zsmul, smul_smul, koszulSign_mul_self, one_smul]

/-- At every missing output block, the normalized whole-weight counit,
with its prescribed pre-Hom parity factor, is the exact stored raw cap
under the specified successor chart. -/
theorem probeOldLeftCounit_missing (i : I) {x y : X}
    (h : x + D.α i = y) (hh : D.h i x < 0)
    (δ : WeightBlocks D Λ x)
    (hδ : ¬ ∃ β, blockSucc D Λ i (sub_add_cancel x (D.α i)) β = δ)
    (M : ProbeOldWeightProduct D Sc m Λ x) :
    koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x) • (((T).leftAdjoints.adjL i h).counit.total M δ) =
      eqToHom (probeOldWeightFollowing_obj D Sc m i Λ h δ M) ≫
        (probeMissingStoredLoc D Sc m δ.1.toList i
          (probeOldBlockTarget_perm D i Λ h δ (blockSucc D Λ i h δ) rfl)
          (by simpa only [Multiset.mem_toList] using
            (show i ∉ δ.1 from fun hm => hδ
              ((exists_blockSucc_iff D Λ i (sub_add_cancel x (D.α i)) δ).mpr hm)))).capL.total (M δ) := by
  have hf := probeOldLeftCounit_negative_sign D Sc m Λ hc i h hh
  have ht := congrArg (fun f : (T).E i h ≫ (T).F i h ⟶ 𝟙 ((T).obj x) => f.total M δ) hf
  have he : koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x) • (((T).leftAdjoints.adjL i h).counit.total M δ) =
      (probeOldWeightLoc D Sc m i Λ (sub_add_cancel x (D.α i)) h (hc i)).capL.total M δ := by
    have hz := congrFun (total_zsmul ((T).leftAdjoints.adjL i h).counit
      (koszulSign (SKM.leftAdjParity D i x) (SKM.leftAdjParity D i x)) M) δ
    exact hz.symm.trans ht
  exact he.trans (probeOldWeightLoc_cap_missing D Sc m i Λ
    (sub_add_cancel x (D.α i)) h δ (hc i) hδ hh M)

end OddMath.QuiverHecke
end

end

section

/-! # Empty-content coordinates of the whole-weight vacuum cap

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
retain the empty-content forgetting map on the upper probe loop and its
full OLD boundary cap. These are the source coordinates required by the
regular-probe evaluation of the chosen central bend.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELV.WeightTensorVacuum
open CyclotomicAction BalancedInduction CyclotomicCrossingTensor
attribute [local irreducible] probeAppendUpperLoopSuperIso
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

/-- Empty-content forgetting retains the selected upper loop literally. -/
theorem forgetEmpty_upper_obj (ν : List I) (hν : ν = []) (i : I)
    (N : ProbeEvaluatedModules D Sc m ν) :
    (emptyContentForget D Sc m ν hν).obj
      ((probeEvaluatedRestriction D Sc m ν i).obj ((probeEvaluatedInduction D Sc m ν i).obj N)) =
    (restriction (oldContentAppend D Sc (probeCutoff D m) [] i)).obj
      ((induction (oldContentAppend D Sc (probeCutoff D m) [] i)).obj
        ((emptyContentForget D Sc m ν hν).obj N)) := by
  subst ν
  rfl

/-- The full boundary cap follows the same empty-content source equality. -/
theorem forgetEmpty_boundary_cap (ν : List I) (hν : ν = []) (i : I)
    (N : ProbeEvaluatedModules D Sc m ν) :
    (emptyContentForget D Sc m ν hν).map
      ((probeEvaluatedMissingCoefficients D Sc m ν i (by rw [hν]; simp)).cap.total N) =
    eqToHom (forgetEmpty_upper_obj D Sc m ν hν i N) ≫
      (contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)).cap.total
        ((emptyContentForget D Sc m ν hν).obj N) := by
  subst ν
  simp only [eqToHom_refl, Category.id_comp]
  change ((probeEvaluatedMissingCoefficients D Sc m [] i (by simp)).cap.total N).hom =
    (contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)).cap.total N.obj
  exact probeEvaluatedMissingCoefficients_cap_total D Sc m [] i (by simp) N

private def totalEvaluation {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A] (M : C) :
    Superfunctor k C A ⥤ A where
  obj F := F.obj M
  map f := f.total M
  map_id F := SuperNatTrans.id_total F.toFunctor M
  map_comp f g := Superfunctor.comp_total f g M

private theorem family_eqToHom {C : Type*} [Category C] (G : C ⥤ C)
    (a : ∀ M, G.obj M ⟶ M) {M N : C} (h : M = N) :
    a M ≫ eqToHom h = G.map (eqToHom h) ≫ a N := by
  subst N
  simp

private theorem emptyBlock_list (Λ : X) :
    (emptyBlock D Λ).1.toList = [] := Multiset.toList_zero

variable (Λ : X) (i : I) {y : X} (edge : -Λ + D.α i = y)
local notation "δ₀" => emptyBlock D Λ
local notation "N₀" => regularProbe D Sc m Λ
local notation "γ₀" => Multiset.toList (Subtype.val (emptyBlock D Λ))
local notation "perm" => probeOldBlockTarget_perm D i Λ edge δ₀ (blockSucc D Λ i edge δ₀) rfl
local notation "F₀" => emptyContentForget D Sc m γ₀ (emptyBlock_list D Λ)
local notation "K" => oldContentAppend D Sc (probeCutoff D m) [] i

/-- The selected successor, upper-loop, and empty-content charts identify
FE of the regular whole-weight probe with the literal native cap source. -/
def vacuumCapSourceIso [Fintype I] :
    (emptyProbe D Sc m Λ).obj
      (((probeOldE D Sc m i Λ edge) ≫ (probeOldF D Sc m i Λ edge)).obj N₀) ≅
      ProbeVacuumCap.source D Sc m i :=
  (F₀).mapIso (eqToIso (probeOldWeightFollowing_obj D Sc m i Λ edge δ₀ N₀)) ≪≫
    (F₀).mapIso ((totalEvaluation (N₀ δ₀)).mapIso
      (probeAppendUpperLoopSuperIso D Sc m γ₀ i perm).symm) ≪≫
    eqToIso (forgetEmpty_upper_obj D Sc m γ₀ (emptyBlock_list D Λ) i (N₀ δ₀)) ≪≫
    ((induction K) ⋙ (restriction K)).mapIso (eqToIso (emptyProbe_regular D Sc m Λ))

/-- The normalized whole-weight left counit at the regular probe is the
prescribed native vacuum cap under the actual FE source chart. The
nontrivial diagonal parity factor is retained explicitly. -/
theorem vacuumLeftCounit_eq [Fintype I]
    (hc : ∀ j, (probeCutoff D m j : ℤ) = D.h j Λ) (hP : 0 < probeCutoff D m i) :
    koszulSign (SKM.leftAdjParity D i (-Λ)) (SKM.leftAdjParity D i (-Λ)) •
      ((emptyProbe D Sc m Λ).map
        (((probeOldRouquierFamily D Sc m Λ hc).leftAdjoints.adjL i edge).counit.total N₀) ≫
          eqToHom (emptyProbe_regular D Sc m Λ)) =
      (vacuumCapSourceIso D Sc m Λ i edge).hom ≫ ProbeVacuumCap.cap D Sc m i hP := by
  have hneg : D.h i (-Λ) = -D.h i Λ := map_neg (D.cd.coroot i) Λ
  have hh : D.h i (-Λ) < 0 := by rw [hneg, ← hc i]; omega
  have hδ : ¬ ∃ β, blockSucc D Λ i (sub_add_cancel (-Λ) (D.α i)) β = δ₀ := by
    rw [exists_blockSucc_iff]
    change i ∉ (0 : Multiset I)
    simp
  have hi : i ∉ γ₀ := by
    change i ∉ (0 : Multiset I).toList
    rw [Multiset.toList_zero]; simp
  have hn : 0 < contentUnitCount D (probeCutoff D m) i (γ₀ : Multiset I) := by
    change 0 < contentUnitCount D (probeCutoff D m) i ((0 : Multiset I).toList : Multiset I)
    rw [Multiset.toList_zero, VacuumCoefficient.count]
    exact hP
  have hw := probeOldLeftCounit_missing D Sc m Λ hc i edge hh δ₀ hδ N₀
  have he := congrArg (F₀).map hw
  rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_comp] at he
  have hs := probeMissingStoredLoc_cap_chart D Sc m γ₀ i perm hi hn
  have hst := congrArg (fun η => η.total (N₀ δ₀)) hs
  rw [Superfunctor.comp_total] at hst
  rw [hst, CategoryTheory.Functor.map_comp,
    forgetEmpty_boundary_cap D Sc m γ₀ (emptyBlock_list D Λ) i (N₀ δ₀)] at he
  have hout := congrArg (fun f => f ≫ eqToHom (emptyProbe_regular D Sc m Λ)) he
  rw [Preadditive.zsmul_comp] at hout
  refine hout.trans ?_
  rw [Category.assoc, Category.assoc, Category.assoc]
  have hN : (F₀).obj (N₀ δ₀) = probeOldVacuumRegular D Sc m := emptyProbe_regular D Sc m Λ
  rw [family_eqToHom ((induction K) ⋙ (restriction K))
    (fun M => (contentMissingBoundaryCoefficients D Sc (probeCutoff D m) [] i (by simp)).cap.total M)
    hN, probeMissingBoundary_regular_cap D Sc m i hP]
  simp only [vacuumCapSourceIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
    totalEvaluation, Iso.symm_hom, Category.assoc]

end OddMath.QuiverHecke.ELV.WeightTensorVacuum
end

end
