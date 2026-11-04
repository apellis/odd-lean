/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirClosures
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPrincipalInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVContentPrincipalInverseCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelClosureDegree
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedContentKernelClosureCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleCentreTotalDegree
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirAbsentClosure

/-! # Represented coordinates of the chosen reservoir closures

BE (1.13)–(1.14), closure dependency G8: the source-coefficient degree
calculation for the chosen closures begins
with their literal unit, principal inverse and cap fields. The prescribed
forward-coordinate squares identify these fields without an inverse premise.
-/
noncomputable section
set_option backward.dsimp.instances true
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ReservoirClosures
open CyclotomicAction BalancedInduction CyclotomicCrossingTensor
universe u
section Composition
variable {C : Type*} [Category C] {V A B A' B' : C}
private theorem closure_coordinates
    (u : V ⟶ A) (p : A ⟶ B) (c : B ⟶ V)
    (a : A ⟶ A') (b : B ⟶ B')
    (u' : V ⟶ A') (p' : A' ⟶ B') (c' : B' ⟶ V)
    (hu : u ≫ a = u') (hp : p ≫ b = a ≫ p') (hc : c = b ≫ c') :
    u ≫ p ≫ c = u' ≫ p' ≫ c' := by
  calc
    u ≫ p ≫ c = u ≫ p ≫ (b ≫ c') := by rw [hc]
    _ = u ≫ (p ≫ b) ≫ c' := by simp only [Category.assoc]
    _ = (u ≫ a) ≫ p' ≫ c' := by rw [hp]; simp only [Category.assoc]
    _ = _ := by rw [hu]
private theorem closure_chart {Z Z' : C}
    (a : A ≅ A') (b : B ≅ B') (c : Z ≅ Z')
    (u : Z ⟶ A) (p : A ⟶ B) (v : B ⟶ Z)
    (u' : Z' ⟶ A') (p' : A' ⟶ B') (v' : B' ⟶ Z')
    (hu : u ≫ a.hom = c.hom ≫ u')
    (hp : p = a.hom ≫ p' ≫ b.inv) (hv : v ≫ c.hom = b.hom ≫ v') :
    (u ≫ p ≫ v) ≫ c.hom = c.hom ≫ u' ≫ p' ≫ v' := by
  calc
    (u ≫ p ≫ v) ≫ c.hom = (u ≫ a.hom) ≫ p' ≫ b.inv ≫ (v ≫ c.hom) := by
      rw [hp]
      simp only [Category.assoc]
    _ = c.hom ≫ u' ≫ p' ≫ v' := by
      rw [hu, hv]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
end Composition

section EvenMaps
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
private theorem even_map_apply {F G : Superfunctor k C (SVec k)}
    (f : F ⟶ G) (hf : f ∈ parity (R := k) F G 0)
    {v w : C} (a : v ⟶ w) (b : F.obj v) :
    f.total w (F.map a b) = G.map a (f.total v b) := by
  have hz (t : C) : f.total t = f.app 0 t := by
    change f.app 0 t + f.app 1 t = f.app 0 t
    rw [Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  rw [hz v, hz w]
  have h := ((Superfunctor.toSuperNatTrans f).isSupernatural 0).naturality_zero a
  simpa only [SVec.comp_apply] using congrArg (fun t : F.obj v ⟶ G.obj w => t b) h
private theorem restriction_map_total
    {A : Type u} [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {F G : Superfunctor k A (SVec k)} (f : F ⟶ G) (w : C) :
    ((BalancedInduction.restriction Q).map f).total w = f.total (Q.obj w) := rfl
private theorem module_action_transport {R S : Superfunctor k C (SVec k)}
    (h : R = S) (η : ∀ M : Superfunctor k C (SVec k), End M)
    {w : C} (a : End w)
    (ha : ∀ b : R.obj w, (η R).total w b = R.map a b) :
    ∀ b : S.obj w, (η S).total w b = S.map a b := by
  cases h
  exact ha
private theorem module_value_transport {R S : Superfunctor k C (SVec k)}
    (h : R = S) (η : ∀ M : Superfunctor k C (SVec k), End M)
    (ha : η R = 0) : η S = 0 := by
  cases h
  exact ha
private theorem module_action_of_family_extension {F : Type*}
    (Q : F → Superfunctor k C (SVec k))
    (e : Superfunctor k C (SVec k) → F)
    (he : ∀ R, Q (e R) = R)
    (η : ∀ R : Superfunctor k C (SVec k), End R)
    (ξ : ∀ M, End (Q M)) {w : C} (a : End w)
    (hη : ∀ M, η (Q M) = ξ M)
    (hξ : ∀ M (b : (Q M).obj w), (ξ M).total w b = (Q M).map a b)
    (R : Superfunctor k C (SVec k)) (b : R.obj w) :
    (η R).total w b = R.map a b := by
  have ha (x : (Q (e R)).obj w) :
      (η (Q (e R))).total w x = (Q (e R)).map a x :=
    (congrArg (fun f : End (Q (e R)) => f.total w x) (hη (e R))).trans (hξ (e R) x)
  exact module_action_transport (k := k) (C := C) (R := Q (e R)) (S := R) (w := w)
    (he R) η a ha b
private def module_centre_action
    (η : End (Superfunctor.id k (Superfunctor k C (SVec k))))
    (R : Superfunctor k C (SVec k)) : End R := η.total R
private def ModuleRepresentedAction
    (η : ∀ R : Superfunctor k C (SVec k), End R) (a : ∀ w : C, End w) : Prop :=
  ∀ (R : Superfunctor k C (SVec k)) (w : C) (b : R.obj w),
    (η R).total w b = R.map (X := w) (Y := w) (a w) b
private theorem module_represented_action_of_family_extension {F : Type*}
    (Q : F → Superfunctor k C (SVec k))
    (e : Superfunctor k C (SVec k) → F)
    (he : ∀ R, Q (e R) = R)
    (η : ∀ R : Superfunctor k C (SVec k), End R)
    (ξ : ∀ M, End (Q M)) (a : ∀ w : C, End w)
    (hη : ∀ M, η (Q M) = ξ M)
    (hξ : ∀ M (w : C) (b : (Q M).obj w),
      (ξ M).total w b = (Q M).map (X := w) (Y := w) (a w) b) :
    ModuleRepresentedAction η a := by
  intro R w b
  exact module_action_of_family_extension Q e he η ξ (w := w) (a w) hη
    (fun M x => hξ M w x) R b
end EvenMaps

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (M : ELVWeightProduct D Sc cutoff N Λ x₁) (β : WeightBlocks D Λ x₀)
local notation "δ" => blockSucc D Λ i h₁ β
local notation "J" => elvBlockAppend D Sc cutoff N i Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff N i Λ h₂ δ
local notation "hDotJ" => elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β
local notation "hDotK" => elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ δ
local notation "Source" => eqToHom (elvWeightMixedSource_obj D Sc cutoff N i i Λ h₁ h₁ β M)
local notation "Target" => eqToHom (elvWeightMixedTarget_obj D Sc cutoff N i i Λ h₁ h₂ h₁ h₂ β M)
local notation "UnitField" r => elvActionUnit D Sc cutoff N i Λ h₂ ≫
  SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) r ▷ elvF D Sc cutoff N i Λ h₂
local notation "CapField" s => elvF D Sc cutoff N i Λ h₁ ◁
  SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) s ≫ elvActionCounit D Sc cutoff N i Λ h₁

/-- The actual positive-weight closure is the content unit, chosen content
cap-principal inverse and content cap, on every supported input block. -/
theorem positive_content_coordinates (hh : 0 ≤ D.h i x₁) (r s : ℕ) :
    (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M δ =
      unitDotColumn K hDotK (M δ) r ≫
        (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).f' ≫
          capDotRow J hDotJ (M δ) s := by
  have hη : ((elvRouquierFamily D Sc cutoff N Λ hcutoff).adj i h₂).unit =
      elvActionUnit D Sc cutoff N i Λ h₂ := rfl
  have hε : ((elvRouquierFamily D Sc cutoff N Λ hcutoff).adj i h₁).counit =
      elvActionCounit D Sc cutoff N i Λ h₁ := rfl
  have hx₁ : (elvRouquierFamily D Sc cutoff N Λ hcutoff).dot i h₁ =
      elvActionDot D Sc cutoff N i Λ h₁ := rfl
  have hx₂ : (elvRouquierFamily D Sc cutoff N Λ hcutoff).dot i h₂ =
      elvActionDot D Sc cutoff N i Λ h₂ := rfl
  have h := closure_coordinates ((UnitField r).total M δ)
    (elvChosenCapPrincipal D Sc cutoff N Λ hcutoff i h₁ h₂ M δ hh)
    ((CapField s).total M δ) (Target) (Source) _ _ _
    (elvWeightUnitPower_localCoordinates D Sc cutoff N i Λ h₁ h₂ β M r)
    (elvChosenCapPrincipal_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh)
    (elvWeightCapPower_localCoordinates D Sc cutoff N i Λ h₁ β M s)
  have hu := congrFun (Superfunctor.comp_total (elvActionUnit D Sc cutoff N i Λ h₂)
    (SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) r ▷ elvF D Sc cutoff N i Λ h₂) M) δ
  have hc := congrFun (Superfunctor.comp_total
    (elvF D Sc cutoff N i Λ h₁ ◁ SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) s)
    (elvActionCounit D Sc cutoff N i Λ h₁) M) δ
  rw [hu, hc] at h
  set_option backward.dsimp.instances true in
    simpa only [positive, elvChosenCapPrincipal, Superfunctor.comp_total, SuperNatTrans.vcomp_total, CategoryTheory.Pi.comp_apply, Category.assoc, hη, hε, hx₁, hx₂, elvRouquierFamily_F] using h

/-- The actual negative-weight closure has the same content coordinates,
using the selected content unit-principal inverse. -/
theorem negative_content_coordinates (hh : D.h i x₁ ≤ 0) (r s : ℕ) :
    (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M δ =
      unitDotColumn K hDotK (M δ) r ≫
        (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).f' ≫
          capDotRow J hDotJ (M δ) s := by
  have hη : ((elvRouquierFamily D Sc cutoff N Λ hcutoff).adj i h₂).unit =
      elvActionUnit D Sc cutoff N i Λ h₂ := rfl
  have hε : ((elvRouquierFamily D Sc cutoff N Λ hcutoff).adj i h₁).counit =
      elvActionCounit D Sc cutoff N i Λ h₁ := rfl
  have hx₁ : (elvRouquierFamily D Sc cutoff N Λ hcutoff).dot i h₁ =
      elvActionDot D Sc cutoff N i Λ h₁ := rfl
  have hx₂ : (elvRouquierFamily D Sc cutoff N Λ hcutoff).dot i h₂ =
      elvActionDot D Sc cutoff N i Λ h₂ := rfl
  have h := closure_coordinates ((UnitField r).total M δ)
    (elvChosenUnitPrincipal D Sc cutoff N Λ hcutoff i h₁ h₂ M δ hh)
    ((CapField s).total M δ) (Target) (Source) _ _ _
    (elvWeightUnitPower_localCoordinates D Sc cutoff N i Λ h₁ h₂ β M r)
    (elvChosenUnitPrincipal_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh)
    (elvWeightCapPower_localCoordinates D Sc cutoff N i Λ h₁ β M s)
  have hu := congrFun (Superfunctor.comp_total (elvActionUnit D Sc cutoff N i Λ h₂)
    (SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) r ▷ elvF D Sc cutoff N i Λ h₂) M) δ
  have hc := congrFun (Superfunctor.comp_total
    (elvF D Sc cutoff N i Λ h₁ ◁ SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) s)
    (elvActionCounit D Sc cutoff N i Λ h₁) M) δ
  rw [hu, hc] at h
  set_option backward.dsimp.instances true in
    simpa only [negative, elvChosenUnitPrincipal, Superfunctor.comp_total, SuperNatTrans.vcomp_total, CategoryTheory.Pi.comp_apply, Category.assoc, hη, hε, hx₁, hx₂, elvRouquierFamily_F] using h

section ContentCoordinates
variable (β₀ : Multiset I)
local notation "γ₀" => β₀ + ([i] : Multiset I)
local notation "δ₀" => γ₀ + ([i] : Multiset I)
local notation "hJ₀" => contentBlockCanonicalSum β₀ [i]
local notation "hK₀" => contentBlockCanonicalSum γ₀ [i]
local notation "J₀" => contentAppendTo D Sc cutoff N β₀ [i] γ₀ hJ₀
local notation "K₀" => contentAppendTo D Sc cutoff N γ₀ [i] δ₀ hK₀
local notation "hCross₀" => contentBlockMatrixCross_supernatural D Sc cutoff N β₀ i
local notation "hDotJ₀" => contentBlockMatrixDot_supernatural D Sc cutoff N β₀ i
local notation "hDotK₀" => contentBlockMatrixDot_supernatural D Sc cutoff N γ₀ i
local notation "Q₀" => contentInclusion D Sc cutoff N γ₀
local notation "T₀" => truncatedAppend D Sc cutoff N [i]
variable (M₀ : ContentModules D Sc cutoff N (β₀ + ([i] : Multiset I)))
local notation "P₀" => induced Q₀ M₀
local notation "Value₀" => contentExtensionUnitIso D Sc cutoff N γ₀ M₀
local notation "Source₀" => contentPrincipalSourceIso D Sc cutoff N β₀ γ₀ i hJ₀ M₀
local notation "Target₀" => contentPrincipalTargetIso D Sc cutoff N γ₀ δ₀ i hK₀ M₀

/-- Every content unit inverse gives the same weighted closure square. -/
theorem contentUnitClosure_coordinates
    (L : SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent J₀ K₀ hCross₀ M₀)
      (unitDotColumn K₀ hDotK₀ M₀) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i γ₀))
    (hh : 0 ≤ contentCrossingHeight D cutoff i γ₀) (r s : ℕ) :
    (unitDotColumn K₀ hDotK₀ M₀ r ≫ L.f' ≫ capDotRow J₀ hDotJ₀ M₀ s) ≫ (Value₀).hom =
      (Value₀).hom ≫
        (restriction Q₀).map (unitDotColumn T₀ (truncatedDot_supernatural D Sc cutoff N i) P₀ r) ≫
          (weightedContentLocalInverseFrom D Sc cutoff N i P₀ γ₀ hh).f' ≫
            (restriction Q₀).map (capDotRow T₀ (truncatedDot_supernatural D Sc cutoff N i) P₀ s) := by
  exact closure_chart (Target₀) (Source₀) (Value₀) _ _ _ _ _ _
    (contentUnitDotColumn_square D Sc cutoff N γ₀ i M₀ r)
    (contentSupportedLocalInverseFrom_principal D Sc cutoff N β₀ i M₀ L hh)
    (contentMatrixCapDotRow_square D Sc cutoff N β₀ i M₀ s)

/-- Every content cap inverse gives the weighted closure square in the other orientation. -/
theorem contentCapClosure_coordinates
    (L : SKM.SuperSumInvTo (k := k) (orderedGridMateComponent J₀ K₀ hCross₀ M₀)
      (capDotRow J₀ hDotJ₀ M₀) (D.parity i) (fun n => n • D.parity i)
      (contentCapCount D cutoff i γ₀))
    (hh : contentCrossingHeight D cutoff i γ₀ ≤ 0) (r s : ℕ) :
    (unitDotColumn K₀ hDotK₀ M₀ r ≫ L.f' ≫ capDotRow J₀ hDotJ₀ M₀ s) ≫ (Value₀).hom =
      (Value₀).hom ≫
        (restriction Q₀).map (unitDotColumn T₀ (truncatedDot_supernatural D Sc cutoff N i) P₀ r) ≫
          (weightedContentLocalInverseTo D Sc cutoff N i P₀ γ₀ hh).f' ≫
            (restriction Q₀).map (capDotRow T₀ (truncatedDot_supernatural D Sc cutoff N i) P₀ s) := by
  exact closure_chart (Target₀) (Source₀) (Value₀) _ _ _ _ _ _
    (contentUnitDotColumn_square D Sc cutoff N γ₀ i M₀ r)
    (contentSupportedLocalInverseTo_principal D Sc cutoff N β₀ i M₀ L hh)
    (contentMatrixCapDotRow_square D Sc cutoff N β₀ i M₀ s)
end ContentCoordinates

private theorem closureSingletonDot_mem (i : I) :
    dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1

section ContentTargets
variable (βt γt δt : Multiset I) (hγt : βt + ([i] : Multiset I) = γt)
  (hδt : γt + ([i] : Multiset I) = δt) (Mt : ContentModules D Sc cutoff N γt)
local notation "Jt" => contentAppendTo D Sc cutoff N βt [i] γt hγt
local notation "Kt" => contentAppendTo D Sc cutoff N γt [i] δt hδt
local notation "hCrosst" => contentTargetsGridCross_supernatural D Sc cutoff N βt γt δt i hγt hδt
local notation "hDotJt" => contentAppendTo_supernatural D Sc cutoff N hγt hγt
  (closureSingletonDot_mem D Sc i)
local notation "hDotKt" => contentAppendTo_supernatural D Sc cutoff N hδt hδt
  (closureSingletonDot_mem D Sc i)
local notation "Qt" => contentInclusion D Sc cutoff N γt
local notation "Tt" => truncatedAppend D Sc cutoff N [i]
local notation "Pt" => induced Qt Mt
local notation "Valuet" => contentExtensionUnitIso D Sc cutoff N γt Mt

/-- Stored successors preserve the weighted closure square in unit orientation. -/
theorem contentTargetsUnitClosure_coordinates
    (L : SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent Jt Kt hCrosst Mt)
      (unitDotColumn Kt hDotKt Mt) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i γt))
    (hh : 0 ≤ contentCrossingHeight D cutoff i γt) (r s : ℕ) :
    (unitDotColumn Kt hDotKt Mt r ≫ L.f' ≫ capDotRow Jt hDotJt Mt s) ≫ (Valuet).hom =
      (Valuet).hom ≫
        (restriction Qt).map (unitDotColumn Tt (truncatedDot_supernatural D Sc cutoff N i) Pt r) ≫
          (weightedContentLocalInverseFrom D Sc cutoff N i Pt γt hh).f' ≫
            (restriction Qt).map (capDotRow Tt (truncatedDot_supernatural D Sc cutoff N i) Pt s) := by
  subst δt
  subst γt
  exact contentUnitClosure_coordinates D Sc cutoff N i βt Mt L hh r s

/-- Stored successors preserve the weighted closure square in cap orientation. -/
theorem contentTargetsCapClosure_coordinates
    (L : SKM.SuperSumInvTo (k := k) (orderedGridMateComponent Jt Kt hCrosst Mt)
      (capDotRow Jt hDotJt Mt) (D.parity i) (fun n => n • D.parity i)
      (contentCapCount D cutoff i γt))
    (hh : contentCrossingHeight D cutoff i γt ≤ 0) (r s : ℕ) :
    (unitDotColumn Kt hDotKt Mt r ≫ L.f' ≫ capDotRow Jt hDotJt Mt s) ≫ (Valuet).hom =
      (Valuet).hom ≫
        (restriction Qt).map (unitDotColumn Tt (truncatedDot_supernatural D Sc cutoff N i) Pt r) ≫
          (weightedContentLocalInverseTo D Sc cutoff N i Pt γt hh).f' ≫
            (restriction Qt).map (capDotRow Tt (truncatedDot_supernatural D Sc cutoff N i) Pt s) := by
  subst δt
  subst γt
  exact contentCapClosure_coordinates D Sc cutoff N i βt Mt L hh r s
end ContentTargets

local notation "Qδ" => contentInclusion D Sc cutoff N δ.1
local notation "Tδ" => truncatedAppend D Sc cutoff N [i]
local notation "Pδ" => induced Qδ (M δ)
local notation "Valueδ" => contentExtensionUnitIso D Sc cutoff N δ.1 (M δ)

include hcutoff in
private theorem cap_height (γ : WeightBlocks D Λ x₁) (hh : 0 ≤ D.h i x₁) :
    contentCrossingHeight D cutoff i γ.1 ≤ 0 := by
  rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x₁ (hcutoff i) γ]
  exact neg_nonpos.mpr hh
include hcutoff in
private theorem unit_height (γ : WeightBlocks D Λ x₁) (hh : D.h i x₁ ≤ 0) :
    0 ≤ contentCrossingHeight D cutoff i γ.1 := by
  rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x₁ (hcutoff i) γ]
  exact neg_nonneg.mpr hh

/-- The chosen positive-weight closure uses the prescribed weighted cap
principal, in the same extension-unit value chart as its forward fields. -/
theorem positive_weighted_coordinates (hh : 0 ≤ D.h i x₁) (r s : ℕ) :
    (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M δ ≫ (Valueδ).hom =
      (Valueδ).hom ≫
        (restriction Qδ).map (unitDotColumn Tδ (truncatedDot_supernatural D Sc cutoff N i) Pδ r) ≫
          (weightedContentLocalInverseTo D Sc cutoff N i Pδ δ.1 (cap_height D cutoff Λ hcutoff i δ hh)).f' ≫
            (restriction Qδ).map (capDotRow Tδ (truncatedDot_supernatural D Sc cutoff N i) Pδ s) := by
  rw [positive_content_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh r s]
  exact contentTargetsCapClosure_coordinates D Sc cutoff N i β.1 δ.1
    (blockSucc D Λ i h₂ δ).1 (elvBlockSucc_content_eq D i Λ h₁ β)
    (elvBlockSucc_content_eq D i Λ h₂ δ) (M δ)
    (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh) (cap_height D cutoff Λ hcutoff i δ hh) r s

/-- The chosen negative-weight closure uses the prescribed weighted unit
principal in that same value chart. -/
theorem negative_weighted_coordinates (hh : D.h i x₁ ≤ 0) (r s : ℕ) :
    (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M δ ≫ (Valueδ).hom =
      (Valueδ).hom ≫
        (restriction Qδ).map (unitDotColumn Tδ (truncatedDot_supernatural D Sc cutoff N i) Pδ r) ≫
          (weightedContentLocalInverseFrom D Sc cutoff N i Pδ δ.1 (unit_height D cutoff Λ hcutoff i δ hh)).f' ≫
            (restriction Qδ).map (capDotRow Tδ (truncatedDot_supernatural D Sc cutoff N i) Pδ s) := by
  rw [negative_content_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh r s]
  exact contentTargetsUnitClosure_coordinates D Sc cutoff N i β.1 δ.1
    (blockSucc D Λ i h₂ δ).1 (elvBlockSucc_content_eq D i Λ h₁ β)
    (elvBlockSucc_content_eq D i Λ h₂ δ) (M δ)
    (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh) (unit_height D cutoff Λ hcutoff i δ hh) r s

section RepresentedValues
variable (γ : WeightBlocks D Λ x₁)

/-- The represented OLD negative-kernel closure in the positive weight orientation. -/
def positiveRepresentedValue (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    (w : ContentCategory D Sc cutoff N γ.1) : w ⟶ w :=
  weightedContentCapClosureCoefficient D Sc cutoff N i γ.1
    (cap_height D cutoff Λ hcutoff i γ hh) w r s

/-- The represented OLD positive-kernel closure in the negative weight orientation. -/
def negativeRepresentedValue (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    (w : ContentCategory D Sc cutoff N γ.1) : w ⟶ w :=
  weightedContentUnitClosureCoefficient D Sc cutoff N i γ.1
    (unit_height D cutoff Λ hcutoff i γ hh) w r s

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The represented positive-weight value has the positive closure degree. -/
theorem positiveRepresentedValue_degree (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    (w : ContentCategory D Sc cutoff N γ.1) :
    positiveRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r s w ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  exact weightedContentCapClosureCoefficient_degree D Sc cutoff N i sy hc γ.1
    (cap_height D cutoff Λ hcutoff i γ hh) w r s

/-- The represented negative-weight value has the same positive degree. -/
theorem negativeRepresentedValue_degree (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    (w : ContentCategory D Sc cutoff N γ.1) :
    negativeRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r s w ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  exact weightedContentUnitClosureCoefficient_degree D Sc cutoff N i sy hc γ.1
    (unit_height D cutoff Λ hcutoff i γ hh) w r s
end RepresentedValues

attribute [local irreducible] positiveKernelClosure negativeKernelClosure

/-- On each supported block, the literal chosen positive closure is the
ordinary action of its represented source value on every module vector. -/
theorem positive_represented_coordinates (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    (w : ContentCategory D Sc cutoff N δ.1) (b : (M δ).obj w) :
    ((positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M δ).total w b =
      (M δ).map (positiveRepresentedValue D Sc cutoff N Λ hcutoff i δ hh r s w) b := by
  apply (moduleIsoLinearEquiv (Valueδ) w).injective
  change (Valueδ).hom.total w
      (((positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M δ).total w b) =
    (Valueδ).hom.total w
      ((M δ).map (positiveRepresentedValue D Sc cutoff N Λ hcutoff i δ hh r s w) b)
  have he := congrArg (fun f => f.total w b)
    (positive_weighted_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh r s)
  simp only [Superfunctor.comp_total, SVec.comp_apply, restriction_map_total] at he
  have hk := weightedContentCapClosureValue_evaluate D Sc cutoff N i Pδ δ.1
    (cap_height D cutoff Λ hcutoff i δ hh) w r s ((Valueδ).hom.total w b)
  have hn := even_map_apply (Valueδ).hom
    (contentUnitValueIso_hom_mem D Sc cutoff N δ.1 (M δ))
    (positiveRepresentedValue D Sc cutoff N Λ hcutoff i δ hh r s w) b
  have h₁ := hk.trans hn.symm
  have h₂ := he.trans h₁
  convert h₂ using 1

/-- The same represented-action identity holds for the chosen negative closure. -/
theorem negative_represented_coordinates (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    (w : ContentCategory D Sc cutoff N δ.1) (b : (M δ).obj w) :
    ((negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M δ).total w b =
      (M δ).map (negativeRepresentedValue D Sc cutoff N Λ hcutoff i δ hh r s w) b := by
  apply (moduleIsoLinearEquiv (Valueδ) w).injective
  change (Valueδ).hom.total w
      (((negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M δ).total w b) =
    (Valueδ).hom.total w
      ((M δ).map (negativeRepresentedValue D Sc cutoff N Λ hcutoff i δ hh r s w) b)
  have he := congrArg (fun f => f.total w b)
    (negative_weighted_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh r s)
  simp only [Superfunctor.comp_total, SVec.comp_apply, restriction_map_total] at he
  have hk := weightedContentUnitClosureValue_evaluate D Sc cutoff N i Pδ δ.1
    (unit_height D cutoff Λ hcutoff i δ hh) w r s ((Valueδ).hom.total w b)
  have hn := even_map_apply (Valueδ).hom
    (contentUnitValueIso_hom_mem D Sc cutoff N δ.1 (M δ))
    (negativeRepresentedValue D Sc cutoff N Λ hcutoff i δ hh r s w) b
  have h₁ := hk.trans hn.symm
  have h₂ := he.trans h₁
  convert h₂ using 1

attribute [local irreducible] positive negative positiveContent negativeContent
  positiveRepresentedValue negativeRepresentedValue

/-- The positive closure attachment acts by the represented coefficient
on every exact-content module at a supported block. -/
theorem positiveContent_represented_coordinates (β : WeightBlocks D Λ x₀)
    (hh : 0 ≤ D.h i x₁) (r s : ℕ) :
    ModuleRepresentedAction (k := k) (C := ContentCategory D Sc cutoff N (blockSucc D Λ i h₁ β).1)
      (module_centre_action (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂
        (blockSucc D Λ i h₁ β) hh r s))
      (fun w => positiveRepresentedValue D Sc cutoff N Λ hcutoff i (blockSucc D Λ i h₁ β) hh r s w) := by
  let ζ := blockSucc D Λ i h₁ β
  exact module_represented_action_of_family_extension (k := k) (C := ContentCategory D Sc cutoff N ζ.1)
    (F := ELVWeightProduct D Sc cutoff N Λ x₁)
    (fun M : ELVWeightProduct D Sc cutoff N Λ x₁ => M ζ)
    (fun L : ContentModules D Sc cutoff N ζ.1 =>
      (WeightCentreBlocks.extension D Sc cutoff N Λ ζ).obj L)
    (fun L => WeightCentreBlocks.extension_obj D Sc cutoff N Λ ζ L)
    (module_centre_action (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ ζ hh r s))
    (fun M => (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M ζ)
    (fun w => positiveRepresentedValue D Sc cutoff N Λ hcutoff i ζ hh r s w)
    (fun M => positiveContent_total D Sc cutoff N Λ hcutoff i h₁ h₂ ζ hh r s M)
    (fun M w x => positive_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh r s w x)

/-- The negative closure attachment has the same all-module represented action. -/
theorem negativeContent_represented_coordinates (β : WeightBlocks D Λ x₀)
    (hh : D.h i x₁ ≤ 0) (r s : ℕ) :
    ModuleRepresentedAction (k := k) (C := ContentCategory D Sc cutoff N (blockSucc D Λ i h₁ β).1)
      (module_centre_action (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂
        (blockSucc D Λ i h₁ β) hh r s))
      (fun w => negativeRepresentedValue D Sc cutoff N Λ hcutoff i (blockSucc D Λ i h₁ β) hh r s w) := by
  let ζ := blockSucc D Λ i h₁ β
  exact module_represented_action_of_family_extension (k := k) (C := ContentCategory D Sc cutoff N ζ.1)
    (F := ELVWeightProduct D Sc cutoff N Λ x₁)
    (fun M : ELVWeightProduct D Sc cutoff N Λ x₁ => M ζ)
    (fun L : ContentModules D Sc cutoff N ζ.1 =>
      (WeightCentreBlocks.extension D Sc cutoff N Λ ζ).obj L)
    (fun L => WeightCentreBlocks.extension_obj D Sc cutoff N Λ ζ L)
    (module_centre_action (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ ζ hh r s))
    (fun M => (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M ζ)
    (fun w => negativeRepresentedValue D Sc cutoff N Λ hcutoff i ζ hh r s w)
    (fun M => negativeContent_total D Sc cutoff N Λ hcutoff i h₁ h₂ ζ hh r s M)
    (fun M w x => negative_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh r s w x)

section ArbitraryOutputs
variable (γ : WeightBlocks D Λ x₁)

/-- The positive content attachment vanishes on every module if its output
block has no lower predecessor. -/
theorem positiveContent_total_absent
    (hγ : ¬ ∃ β₁, blockSucc D Λ i h₁ β₁ = γ)
    (hh : 0 ≤ D.h i x₁) (r s : ℕ) (R : ContentModules D Sc cutoff N γ.1) :
    (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s).total R = 0 := by
  let M' := (WeightCentreBlocks.extension D Sc cutoff N Λ γ).obj R
  have ha : (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s).total (M' γ) = 0 := by
    rw [positiveContent_total D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s M',
      positive_total_absent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hγ hh r s M']
  exact module_value_transport (WeightCentreBlocks.extension_obj D Sc cutoff N Λ γ R)
    (fun L => (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s).total L) ha

/-- The negative content attachment also vanishes without a predecessor. -/
theorem negativeContent_total_absent
    (hγ : ¬ ∃ β₁, blockSucc D Λ i h₁ β₁ = γ)
    (hh : D.h i x₁ ≤ 0) (r s : ℕ) (R : ContentModules D Sc cutoff N γ.1) :
    (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s).total R = 0 := by
  let M' := (WeightCentreBlocks.extension D Sc cutoff N Λ γ).obj R
  have ha : (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s).total (M' γ) = 0 := by
    rw [negativeContent_total D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s M',
      negative_total_absent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hγ hh r s M']
  exact module_value_transport (WeightCentreBlocks.extension_obj D Sc cutoff N Λ γ R)
    (fun L => (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s).total L) ha

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The reconstructed coefficient of the actual chosen positive closure has
its prescribed strictly positive source integer degree, on every output block. -/
theorem positiveCoefficient_mem_degree (hh : 0 ≤ D.h i x₁) (r s : ℕ) :
    positiveCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s ∈
      contentCoefficientDegree D Sc cutoff N γ.1 sy hc (2 * sy.d i * (r + s + 1 : ℕ)) := by
  change ModuleCentre.reconstruct D Sc cutoff N γ.1
    (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s) ∈ _
  apply ModuleCentre.reconstruct_mem_degree_of_total_evaluation
  intro w
  by_cases hγ : ∃ β₁, blockSucc D Λ i h₁ β₁ = γ
  · rcases hγ with ⟨β₁, rfl⟩
    have he := positiveContent_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ β₁ hh r s
      (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w) w (𝟙 w)
    change ((positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂
      (blockSucc D Λ i h₁ β₁) hh r s).total
      (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w)).total w (𝟙 w) = _ at he
    erw [he]
    change (𝟙 w ≫ positiveRepresentedValue D Sc cutoff N Λ hcutoff i
      (blockSucc D Λ i h₁ β₁) hh r s w) ∈ _
    rw [Category.id_comp]
    exact positiveRepresentedValue_degree D Sc cutoff N Λ hcutoff i
      (blockSucc D Λ i h₁ β₁) sy hc hh r s w
  · rw [positiveContent_total_absent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hγ hh r s,
      supernatural_zero_total, SVec.zero_apply]
    exact Submodule.zero_mem _

/-- The actual chosen negative closure has a source coefficient in the same
strictly positive integer degree, including blocks without predecessors. -/
theorem negativeCoefficient_mem_degree (hh : D.h i x₁ ≤ 0) (r s : ℕ) :
    negativeCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s ∈
      contentCoefficientDegree D Sc cutoff N γ.1 sy hc (2 * sy.d i * (r + s + 1 : ℕ)) := by
  change ModuleCentre.reconstruct D Sc cutoff N γ.1
    (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r s) ∈ _
  apply ModuleCentre.reconstruct_mem_degree_of_total_evaluation
  intro w
  by_cases hγ : ∃ β₁, blockSucc D Λ i h₁ β₁ = γ
  · rcases hγ with ⟨β₁, rfl⟩
    have he := negativeContent_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ β₁ hh r s
      (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w) w (𝟙 w)
    change ((negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂
      (blockSucc D Λ i h₁ β₁) hh r s).total
      (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w)).total w (𝟙 w) = _ at he
    erw [he]
    change (𝟙 w ≫ negativeRepresentedValue D Sc cutoff N Λ hcutoff i
      (blockSucc D Λ i h₁ β₁) hh r s w) ∈ _
    rw [Category.id_comp]
    exact negativeRepresentedValue_degree D Sc cutoff N Λ hcutoff i
      (blockSucc D Λ i h₁ β₁) sy hc hh r s w
  · rw [negativeContent_total_absent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hγ hh r s,
      supernatural_zero_total, SVec.zero_apply]
    exact Submodule.zero_mem _
end ArbitraryOutputs

end OddMath.QuiverHecke.ELVOld.ReservoirClosures
