import OddMath.QuiverHecke.CyclotomicAction.WeightDenominators
import OddMath.QuiverHecke.CyclotomicAction.WeightTripleComparison
import OddMath.QuiverHecke.CyclotomicAction.ContentTriple
import OddMath.QuiverHecke.CyclotomicAction.KernelEntryDegrees
import OddMath.QuiverHecke.CyclotomicAction.WeightedKernel
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.FactorClosures
import OddMath.QuiverHecke.CyclotomicAction.TensorWords

/-!
# Reservoir closure

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Exact-content attachment of the chosen reservoir closures

The principal inverse is the field selected by `elvRouquierFamily.loc`.
The comparison with every whole-weight input follows from naturality,
without an independently supplied comparison or a module-Hom grading.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ReservoirClosures
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The literal positive-height chosen cup-dot/principal/dot-cap closure. -/
def positive (hh : 0 ≤ D.h i x₁) (r s : ℕ) :
    End (Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x₁)) :=
  ((W).adj i h₂).unit ≫ SKM.rouquierPower ((W).dot i h₂) r ▷ (W).F i h₂ ≫
    (((W).loc i h₁ h₂).invPos hh).f' ≫
      ((W).F i h₁ ◁ SKM.rouquierPower ((W).dot i h₁) s ≫ ((W).adj i h₁).counit)

/-- The literal negative-height chosen cup-dot/principal/dot-cap closure. -/
def negative (hh : D.h i x₁ ≤ 0) (r s : ℕ) :
    End (Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x₁)) :=
  ((W).adj i h₂).unit ≫ SKM.rouquierPower ((W).dot i h₂) r ▷ (W).F i h₂ ≫
    (((W).loc i h₁ h₂).invNeg hh).f' ≫
      ((W).F i h₁ ◁ SKM.rouquierPower ((W).dot i h₁) s ≫ ((W).adj i h₁).counit)

variable (β : WeightBlocks D Λ x₁)

def positiveContent (hh : 0 ≤ D.h i x₁) (r s : ℕ) : ModuleCentre.Centre D Sc cutoff N β.1 :=
  WeightCentreBlocks.restrict D Sc cutoff N Λ β (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s)
def negativeContent (hh : D.h i x₁ ≤ 0) (r s : ℕ) : ModuleCentre.Centre D Sc cutoff N β.1 :=
  WeightCentreBlocks.restrict D Sc cutoff N Λ β (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s)

/-- Literal whole-weight closure, at its selected output content, on every input. -/
theorem positiveContent_total (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s).total (M β) =
      (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M β :=
  WeightCentreBlocks.restrict_total D Sc cutoff N Λ β _ M

theorem negativeContent_total (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s).total (M β) =
      (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M β :=
  WeightCentreBlocks.restrict_total D Sc cutoff N Λ β _ M

/-- The recovered source coefficient of the actual positive closure. -/
def positiveCoefficient (hh : 0 ≤ D.h i x₁) (r s : ℕ) : ContentCoefficient D Sc cutoff N β.1 :=
  ModuleCentre.reconstruct D Sc cutoff N β.1 (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s)
def negativeCoefficient (hh : D.h i x₁ ≤ 0) (r s : ℕ) : ContentCoefficient D Sc cutoff N β.1 :=
  ModuleCentre.reconstruct D Sc cutoff N β.1 (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s)

end OddMath.QuiverHecke.ELVOld.ReservoirClosures
end

end

section

/-! # Vanishing of reservoir closures at absent predecessors

The source-coefficient closure calculation of ReservoirClosureDegree also
covers blocks without a lower predecessor. The literal chosen closure
factors through the zero lower induction component, independently of the
principal inverse choice and all dot powers.
-/
noncomputable section
set_option backward.dsimp.instances true
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ReservoirClosures
open CyclotomicAction
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (δ : WeightBlocks D Λ x₁)
  (hδ : ¬ ∃ β, blockSucc D Λ i h₁ β = δ)
include hδ

/-- The actual positive chosen closure vanishes on every absent predecessor
block, for every input family and every pair of dot powers. -/
theorem positive_total_absent (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M δ = 0 := by
  have hz := elvInductionComponent_isZero D Sc cutoff N i Λ h₁ δ hδ
    ((elvF D Sc cutoff N i Λ h₁).obj M)
  have hc : (elvActionAdjunction D Sc cutoff N i Λ h₁).counit.total M δ = 0 := hz.eq_of_src _ 0
  dsimp only [positive, elvRouquierFamily, elvRouquierData]
  simp only [Superfunctor.comp_total, Pi.comp_apply]
  rw [hc, Limits.comp_zero, Limits.comp_zero, Limits.comp_zero, Limits.comp_zero]

/-- The actual negative chosen closure has the same absent-block vanishing. -/
theorem negative_total_absent (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M δ = 0 := by
  have hz := elvInductionComponent_isZero D Sc cutoff N i Λ h₁ δ hδ
    ((elvF D Sc cutoff N i Λ h₁).obj M)
  have hc : (elvActionAdjunction D Sc cutoff N i Λ h₁).counit.total M δ = 0 := hz.eq_of_src _ 0
  dsimp only [negative, elvRouquierFamily, elvRouquierData]
  simp only [Superfunctor.comp_total, Pi.comp_apply]
  rw [hc, Limits.comp_zero, Limits.comp_zero, Limits.comp_zero, Limits.comp_zero]

end OddMath.QuiverHecke.ELVOld.ReservoirClosures
end

end

section

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
end

end

section

/-! # The chosen reservoir closures in the content coefficient ideal

SwappedHomInversion §4, condition (J): the literal chosen principal
closures act through positive-degree source coefficients at each exact
content. Their post-whiskering actions, with arbitrary morphisms on either
side, therefore lie in the jointly nilpotent first coefficient level.
The bound is contentwise; no whole-weight nilpotence bound is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ReservoirClosures
open SwappedAssembly CyclotomicAction
universe u
local instance closureIdealHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₁) (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The entire positive closure belongs to the source coefficient grading. -/
theorem positiveContent_mem_coeffGrading (hh : 0 ≤ D.h i x₁) (r s : ℕ) :
    positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s ∈
      (contentModuleCoeffGrading D Sc cutoff N β.1 sy hc).deg
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  refine ⟨positiveCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s,
    positiveCoefficient_mem_degree D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh r s, ?_⟩
  exact ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _

/-- The negative closure has the same positive coefficient degree. -/
theorem negativeContent_mem_coeffGrading (hh : D.h i x₁ ≤ 0) (r s : ℕ) :
    negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s ∈
      (contentModuleCoeffGrading D Sc cutoff N β.1 sy hc).deg
        (2 * sy.d i * (r + s + 1 : ℕ)) := by
  refine ⟨negativeCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s,
    negativeCoefficient_mem_degree D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh r s, ?_⟩
  exact ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _

variable [Finite I] (T : PiSCat k)

/-- Arbitrary Hom-sector morphisms may surround the positive closure. -/
theorem positiveContent_sandwich_mem (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1}
    (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s) ≫ b) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGrading D Sc cutoff N β.1 sy hc)
    (m := 2 * sy.d i * (r + s + 1 : ℕ))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r + s + 1 : ℕ) := by positivity
    have hd : (0 : ℤ) < 2 * sy.d i * (r + s + 1 : ℕ) := by positivity
    omega
  · exact positiveContent_mem_coeffGrading D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh r s

/-- Arbitrary Hom-sector morphisms may surround the negative closure. -/
theorem negativeContent_sandwich_mem (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1}
    (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s) ≫ b) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGrading D Sc cutoff N β.1 sy hc)
    (m := 2 * sy.d i * (r + s + 1 : ℕ))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r + s + 1 : ℕ) := by positivity
    have hd : (0 : ℤ) < 2 * sy.d i * (r + s + 1 : ℕ) := by positivity
    omega
  · exact negativeContent_mem_coeffGrading D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh r s

/-- Projection of the chosen whole-weight positive closure action lies in the
content coefficient ideal, with arbitrary surrounding transformations. -/
theorem positiveAction_evaluate_mem (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z
          (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact positiveContent_sandwich_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc T hh r s
    (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight b (elvBlockEval D Sc cutoff N Λ β))

/-- Projection of the chosen whole-weight negative closure action lies in the
content coefficient ideal, with arbitrary surrounding transformations. -/
theorem negativeAction_evaluate_mem (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z
          (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact negativeContent_sandwich_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc T hh r s
    (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight b (elvBlockEval D Sc cutoff N Λ β))

local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The literal native positive principal contraction, after output
projection and arbitrary surrounding maps, belongs to the content ideal. -/
theorem positiveClosure_evaluate_mem
    (TF : X → PiSCat.{u,u,u + 1} k) (betaP : I →₀ ℕ) (muP : X)
    (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc (TF (-muP))).mem 1
      (Superfunctor.whiskerRight
        (a ≫ (SKM.homContentPostCup TF W i betaP muP h₂ r Z ≫
          (SKM.homContentPostInvPos TF W i betaP muP h₁ h₂ hh Z).f' ≫
          SKM.homContentPostCap TF W i betaP muP h₁ s Z) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCapInverse_closure TF W i betaP muP h₁ h₂ hh Z r s]
  simpa only [positive, Category.assoc] using
    positiveAction_evaluate_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc (TF (-muP)) hh r s a b

/-- The literal native negative principal contraction, after output
projection and arbitrary surrounding maps, belongs to the content ideal. -/
theorem negativeClosure_evaluate_mem
    (TF : X → PiSCat.{u,u,u + 1} k) (betaP : I →₀ ℕ) (muP : X)
    (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁}
    (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc (TF (-muP))).mem 1
      (Superfunctor.whiskerRight
        (a ≫ (SKM.homContentPostCup TF W i betaP muP h₂ r Z ≫
          (SKM.homContentPostInvNeg TF W i betaP muP h₁ h₂ hh Z).f' ≫
          SKM.homContentPostCap TF W i betaP muP h₁ s Z) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCupInverse_closure TF W i betaP muP h₁ h₂ hh Z r s]
  simpa only [negative, Category.assoc] using
    negativeAction_evaluate_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc (TF (-muP)) hh r s a b

end OddMath.QuiverHecke.ELVOld.ReservoirClosures
end

end

section

/-! # Exact-content source coefficients of the chosen reservoir boundaries

SwappedHomInversion §4 (7): these are the literal `W.loc.boundaryPos` and
`boundaryNeg`, restricted to exact content and reconstructed as source
coefficients. The action comparison follows from naturality on every input.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ReservoirBoundaries
open CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The literal chosen positive-height finite cap boundary. -/
def positive (hh : 0 ≤ D.h i x₁) (j r : ℕ) :
    End (Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x₁)) :=
  ((W).loc i h₁ h₂).boundaryPos hh j r

/-- The literal chosen negative-height finite unit boundary. -/
def negative (hh : D.h i x₁ ≤ 0) (r j : ℕ) :
    End (Superfunctor.id k (ELVWeightProduct D Sc cutoff N Λ x₁)) :=
  ((W).loc i h₁ h₂).boundaryNeg hh r j

variable (β : WeightBlocks D Λ x₁)

def positiveContent (hh : 0 ≤ D.h i x₁) (r s : ℕ) : ModuleCentre.Centre D Sc cutoff N β.1 :=
  WeightCentreBlocks.restrict D Sc cutoff N Λ β (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s)
def negativeContent (hh : D.h i x₁ ≤ 0) (r s : ℕ) : ModuleCentre.Centre D Sc cutoff N β.1 :=
  WeightCentreBlocks.restrict D Sc cutoff N Λ β (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s)

/-- Literal whole-weight boundary contraction, at its selected output content, on every input. -/
theorem positiveContent_total (hh : 0 ≤ D.h i x₁) (r s : ℕ)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s).total (M β) =
      (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M β :=
  WeightCentreBlocks.restrict_total D Sc cutoff N Λ β _ M

theorem negativeContent_total (hh : D.h i x₁ ≤ 0) (r s : ℕ)
    (M : ELVWeightProduct D Sc cutoff N Λ x₁) :
    (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s).total (M β) =
      (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r s).total M β :=
  WeightCentreBlocks.restrict_total D Sc cutoff N Λ β _ M

/-- The recovered source coefficient of the actual positive boundary contraction. -/
def positiveCoefficient (hh : 0 ≤ D.h i x₁) (r s : ℕ) : ContentCoefficient D Sc cutoff N β.1 :=
  ModuleCentre.reconstruct D Sc cutoff N β.1 (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s)
def negativeCoefficient (hh : D.h i x₁ ≤ 0) (r s : ℕ) : ContentCoefficient D Sc cutoff N β.1 :=
  ModuleCentre.reconstruct D Sc cutoff N β.1 (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r s)

end OddMath.QuiverHecke.ELVOld.ReservoirBoundaries
end

end

section

/-! # Chosen reservoir boundary contractions in source coordinates

SwappedHomInversion §4 (7): the finite chosen `g'` fields retain their
weight, content, parity and raw OLD coefficient coordinates. Supported
blocks use the prescribed local matrices; absent unit windows are retained.
-/
noncomputable section
set_option backward.dsimp.instances true
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ReservoirBoundaries
open CyclotomicAction BalancedInduction CyclotomicCrossingTensor
universe u
attribute [local irreducible] positive negative positiveContent negativeContent
  weightedContentUnitBoundaryCoefficient
  weightedContentCapBoundaryCoefficient weightedContentUnitBoundaryValue
  weightedContentCapBoundaryValue

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

/-- The literal chosen positive boundary has the content cap inverse column. -/
theorem positive_content_coordinates (hh : 0 ≤ D.h i x₁)
    (j : ℕ) (hj : j < (D.h i x₁).toNat) (r : ℕ) :
    (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh j r).total M δ =
      (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).g' j ≫
        capDotRow J hDotJ (M δ) r := by
  have hp := elvChosenCapWindow_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh j hj
  have hc := elvWeightCapPower_localCoordinates D Sc cutoff N i Λ h₁ β M r
  have h : elvChosenCapWindow D Sc cutoff N Λ hcutoff i h₁ h₂ M δ hh j ≫
      (CapField r).total M δ =
      (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).g' j ≫
        capDotRow J hDotJ (M δ) r := by
    rw [hc, ← Category.assoc, hp]
  dsimp only [elvChosenCapWindow] at h
  have hcomp := congrFun (Superfunctor.comp_total
    ((((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invPos hh).g' j)
    (CapField r) M) δ
  change _ =
    (((((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invPos hh).g' j).total M δ ≫
      (CapField r).total M δ) at hcomp
  rw [← hcomp] at h
  have hε : ((elvRouquierFamily D Sc cutoff N Λ hcutoff).adj i h₁).counit =
      elvActionCounit D Sc cutoff N i Λ h₁ := rfl
  have hx : (elvRouquierFamily D Sc cutoff N Λ hcutoff).dot i h₁ =
      elvActionDot D Sc cutoff N i Λ h₁ := rfl
  simpa only [positive, SKM.SuperRouquierLoc.boundaryPos,
    Category.assoc, hε, hx, elvRouquierFamily_F] using h

/-- The literal chosen negative boundary has the content unit inverse row. -/
theorem negative_content_coordinates (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j).total M δ =
      unitDotColumn K hDotK (M δ) r ≫
        (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).g' j := by
  have hp := elvChosenUnitWindow_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh j hj
  have hu := elvWeightUnitPower_localCoordinates D Sc cutoff N i Λ h₁ h₂ β M r
  have h : (UnitField r).total M δ ≫
      elvChosenUnitWindow D Sc cutoff N Λ hcutoff i h₁ h₂ M δ hh j =
      unitDotColumn K hDotK (M δ) r ≫
        (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh).g' j := by
    rw [hp, ← Category.assoc, hu]
  dsimp only [elvChosenUnitWindow] at h
  have hcomp := congrFun (Superfunctor.comp_total (UnitField r)
    ((((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invNeg hh).g' j) M) δ
  change _ = ((UnitField r).total M δ ≫
    ((((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invNeg hh).g' j).total M δ) at hcomp
  rw [← hcomp] at h
  have hη : ((elvRouquierFamily D Sc cutoff N Λ hcutoff).adj i h₂).unit =
      elvActionUnit D Sc cutoff N i Λ h₂ := rfl
  have hx : (elvRouquierFamily D Sc cutoff N Λ hcutoff).dot i h₂ =
      elvActionDot D Sc cutoff N i Λ h₂ := rfl
  simpa only [negative, SKM.SuperRouquierLoc.boundaryNeg,
    Category.assoc, hη, hx, elvRouquierFamily_F] using h

private theorem boundarySingletonDot_mem (i : I) :
    dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1

section ContentTargets
variable (βt γt δt : Multiset I) (hγt : βt + ([i] : Multiset I) = γt)
  (hδt : γt + ([i] : Multiset I) = δt) (Mt : ContentModules D Sc cutoff N γt)
local notation "Jt" => contentAppendTo D Sc cutoff N βt [i] γt hγt
local notation "Kt" => contentAppendTo D Sc cutoff N γt [i] δt hδt
local notation "hCrosst" => contentTargetsGridCross_supernatural D Sc cutoff N βt γt δt i hγt hδt
local notation "hDotJt" => contentAppendTo_supernatural D Sc cutoff N hγt hγt
  (boundarySingletonDot_mem D Sc i)
local notation "hDotKt" => contentAppendTo_supernatural D Sc cutoff N hδt hδt
  (boundarySingletonDot_mem D Sc i)
local notation "Qt" => contentInclusion D Sc cutoff N γt
local notation "Tt" => truncatedAppend D Sc cutoff N [i]
local notation "Pt" => induced Qt Mt
local notation "Valuet" => contentExtensionUnitIso D Sc cutoff N γt Mt
local notation "Sourcet" => contentPrincipalSourceIso D Sc cutoff N βt γt i hγt Mt
local notation "Targett" => contentPrincipalTargetIso D Sc cutoff N γt δt i hδt Mt

/-- The content cap boundary retains the weighted finite inverse column. -/
theorem contentTargetsCapBoundary_coordinates
    (L : SKM.SuperSumInvTo (k := k) (orderedGridMateComponent Jt Kt hCrosst Mt)
      (capDotRow Jt hDotJt Mt) (D.parity i) (fun n => n • D.parity i)
      (contentCapCount D cutoff i γt))
    (hh : contentCrossingHeight D cutoff i γt ≤ 0)
    (j : ℕ) (hj : j < contentCapCount D cutoff i γt) (r : ℕ) :
    (L.g' j ≫ capDotRow Jt hDotJt Mt r) ≫ (Valuet).hom =
      (Valuet).hom ≫ (weightedContentLocalInverseTo D Sc cutoff N i Pt γt hh).g' j ≫
        (restriction Qt).map (capDotRow Tt (truncatedDot_supernatural D Sc cutoff N i) Pt r) := by
  rw [contentTargetsLocalInverseTo_window D Sc cutoff N βt i γt δt hγt hδt Mt L hh j hj]
  -- The same ordinary cap square with the stored successor contents.
  have hc' : capDotRow Jt hDotJt Mt r ≫ (Valuet).hom =
      (Sourcet).hom ≫
        (restriction Qt).map (capDotRow Tt (truncatedDot_supernatural D Sc cutoff N i) Pt r) := by
    subst δt
    subst γt
    exact contentMatrixCapDotRow_square D Sc cutoff N βt i Mt r
  simp only [Category.assoc]
  rw [hc']
  simp only [Iso.inv_hom_id_assoc]

/-- The content unit boundary retains the weighted finite inverse row. -/
theorem contentTargetsUnitBoundary_coordinates
    (L : SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent Jt Kt hCrosst Mt)
      (unitDotColumn Kt hDotKt Mt) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i γt))
    (hh : 0 ≤ contentCrossingHeight D cutoff i γt)
    (r j : ℕ) (hj : j < contentUnitCount D cutoff i γt) :
    (unitDotColumn Kt hDotKt Mt r ≫ L.g' j) ≫ (Valuet).hom =
      (Valuet).hom ≫
        (restriction Qt).map (unitDotColumn Tt (truncatedDot_supernatural D Sc cutoff N i) Pt r) ≫
          (weightedContentLocalInverseFrom D Sc cutoff N i Pt γt hh).g' j := by
  rw [contentTargetsLocalInverseFrom_window D Sc cutoff N βt i γt δt hγt hδt Mt L hh j hj]
  have hu' : unitDotColumn Kt hDotKt Mt r ≫ (Targett).hom =
      (Valuet).hom ≫
        (restriction Qt).map (unitDotColumn Tt (truncatedDot_supernatural D Sc cutoff N i) Pt r) := by
    subst δt
    subst γt
    exact contentUnitDotColumn_square D Sc cutoff N (βt + ([i] : Multiset I)) i Mt r
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, hu']
  simp only [Category.assoc]
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

/-- The chosen positive boundary has the literal weighted cap-window coordinates. -/
theorem positive_weighted_coordinates (hh : 0 ≤ D.h i x₁)
    (j : ℕ) (hj : j < (D.h i x₁).toNat) (r : ℕ) :
    (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh j r).total M δ ≫ (Valueδ).hom =
      (Valueδ).hom ≫
        (weightedContentLocalInverseTo D Sc cutoff N i Pδ δ.1
          (cap_height D cutoff Λ hcutoff i δ hh)).g' j ≫
        (restriction Qδ).map (capDotRow Tδ (truncatedDot_supernatural D Sc cutoff N i) Pδ r) := by
  rw [positive_content_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh j hj r]
  exact contentTargetsCapBoundary_coordinates D Sc cutoff N i β.1 δ.1
    (blockSucc D Λ i h₂ δ).1 (elvBlockSucc_content_eq D i Λ h₁ β)
    (elvBlockSucc_content_eq D i Λ h₂ δ) (M δ)
    (elvContentCapInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh)
    (cap_height D cutoff Λ hcutoff i δ hh) j
    (by simpa only [contentCapCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ] using hj) r

/-- The chosen negative boundary has the literal weighted unit-window coordinates. -/
theorem negative_weighted_coordinates (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j).total M δ ≫ (Valueδ).hom =
      (Valueδ).hom ≫
        (restriction Qδ).map (unitDotColumn Tδ (truncatedDot_supernatural D Sc cutoff N i) Pδ r) ≫
          (weightedContentLocalInverseFrom D Sc cutoff N i Pδ δ.1
            (unit_height D cutoff Λ hcutoff i δ hh)).g' j := by
  rw [negative_content_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh r j hj]
  exact contentTargetsUnitBoundary_coordinates D Sc cutoff N i β.1 δ.1
    (blockSucc D Λ i h₂ δ).1 (elvBlockSucc_content_eq D i Λ h₁ β)
    (elvBlockSucc_content_eq D i Λ h₂ δ) (M δ)
    (elvContentUnitInverseAtWeight D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh)
    (unit_height D cutoff Λ hcutoff i δ hh) r j
    (by simpa only [contentUnitCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ] using hj)

private theorem upperUnitColumn_square (γt δt : Multiset I)
    (hδt : γt + ([i] : Multiset I) = δt) (Mt : ContentModules D Sc cutoff N γt) (r : ℕ) :
    unitDotColumn (contentAppendTo D Sc cutoff N γt [i] δt hδt)
      (contentAppendTo_supernatural D Sc cutoff N hδt hδt (boundarySingletonDot_mem D Sc i)) Mt r ≫
      (contentPrincipalTargetIso D Sc cutoff N γt δt i hδt Mt).hom =
    (contentExtensionUnitIso D Sc cutoff N γt Mt).hom ≫
      (restriction (contentInclusion D Sc cutoff N γt)).map
        (unitDotColumn (truncatedAppend D Sc cutoff N [i])
          (truncatedDot_supernatural D Sc cutoff N i)
          (induced (contentInclusion D Sc cutoff N γt) Mt) r) := by
  subst δt
  exact contentUnitDotColumn_square D Sc cutoff N γt i Mt r

section ArbitraryOutputs
variable (γ : WeightBlocks D Λ x₁)
local notation "Qγ" => contentInclusion D Sc cutoff N (Subtype.val γ)
local notation "Tγ" => truncatedAppend D Sc cutoff N [i]
local notation "Pγ" => induced Qγ (M γ)
local notation "Valueγ" => contentExtensionUnitIso D Sc cutoff N (Subtype.val γ) (M γ)
local notation "εγ" => blockSucc D Λ i h₂ γ
local notation "Kγ" => elvBlockAppend D Sc cutoff N i Λ h₂ γ
local notation "hDotKγ" => elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ γ

/-- At an absent predecessor, the chosen unit boundary retains the finite content row. -/
theorem negative_absent_content_coordinates
    (hγ : ¬ ∃ β₁, blockSucc D Λ i h₁ β₁ = γ) (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j).total M γ =
      unitDotColumn Kγ hDotKγ (M γ) r ≫
        (elvContentAbsentUnitInverseAtWeight D Sc cutoff N Λ i h₁ h₂ M γ hγ).g' j := by
  have hp := elvChosenAbsentUnitWindow_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M γ hγ hh j hj
  have hu := elvWeightUnitPower_following_coordinates D Sc cutoff N Λ i h₂ M γ r
  have h : (UnitField r).total M γ ≫
      elvChosenUnitWindow D Sc cutoff N Λ hcutoff i h₁ h₂ M γ hh j =
      unitDotColumn Kγ hDotKγ (M γ) r ≫
        (elvContentAbsentUnitInverseAtWeight D Sc cutoff N Λ i h₁ h₂ M γ hγ).g' j := by
    rw [hp, ← Category.assoc, hu]
  dsimp only [elvChosenUnitWindow] at h
  have hcomp := congrFun (Superfunctor.comp_total (UnitField r)
    ((((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invNeg hh).g' j) M) γ
  change _ = ((UnitField r).total M γ ≫
    ((((elvRouquierFamily D Sc cutoff N Λ hcutoff).loc i h₁ h₂).invNeg hh).g' j).total M γ) at hcomp
  rw [← hcomp] at h
  have hη : ((elvRouquierFamily D Sc cutoff N Λ hcutoff).adj i h₂).unit =
      elvActionUnit D Sc cutoff N i Λ h₂ := rfl
  have hx : (elvRouquierFamily D Sc cutoff N Λ hcutoff).dot i h₂ =
      elvActionDot D Sc cutoff N i Λ h₂ := rfl
  simpa only [negative, SKM.SuperRouquierLoc.boundaryNeg,
    Category.assoc, hη, hx, elvRouquierFamily_F] using h

/-- Absence preserves the weighted finite unit boundary; no vanishing is asserted. -/
theorem negative_absent_weighted_coordinates
    (hγ : ¬ ∃ β₁, blockSucc D Λ i h₁ β₁ = γ) (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j).total M γ ≫ (Valueγ).hom =
      (Valueγ).hom ≫
        (restriction Qγ).map (unitDotColumn Tγ (truncatedDot_supernatural D Sc cutoff N i) Pγ r) ≫
          (weightedContentLocalInverseFrom D Sc cutoff N i Pγ γ.1
            (unit_height D cutoff Λ hcutoff i γ hh)).g' j := by
  rw [negative_absent_content_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M γ hγ hh r j hj]
  have hj' : j < contentUnitCount D cutoff i γ.1 := by
    simpa only [contentUnitCount_weightBlock D cutoff i Λ x₁ (hcutoff i) γ] using hj
  rw [contentAbsentUnitTargetInverse_window D Sc cutoff N γ.1 εγ.1 i
    (elvBlockSucc_content_eq D i Λ h₂ γ) (M γ)
    (elvContentAbsentUnitInverseAtWeight D Sc cutoff N Λ i h₁ h₂ M γ hγ)
    (unit_height D cutoff Λ hcutoff i γ hh) j hj']
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, upperUnitColumn_square D Sc cutoff N i γ.1 εγ.1
    (elvBlockSucc_content_eq D i Λ h₂ γ) (M γ) r]
  simp only [Category.assoc]

/-- Every output block retains the same chosen weighted finite unit boundary. -/
theorem negative_weighted_coordinates_all (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j).total M γ ≫ (Valueγ).hom =
      (Valueγ).hom ≫
        (restriction Qγ).map (unitDotColumn Tγ (truncatedDot_supernatural D Sc cutoff N i) Pγ r) ≫
          (weightedContentLocalInverseFrom D Sc cutoff N i Pγ γ.1
            (unit_height D cutoff Λ hcutoff i γ hh)).g' j := by
  by_cases hγ : ∃ β₁, blockSucc D Λ i h₁ β₁ = γ
  · rcases hγ with ⟨β₁, rfl⟩
    exact negative_weighted_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β₁ hh r j hj
  · exact negative_absent_weighted_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M γ hγ hh r j hj

/-- The represented cap-boundary source value at positive weight height. -/
def positiveRepresentedValue (hh : 0 ≤ D.h i x₁)
    (j r : ℕ) (hj : j < (D.h i x₁).toNat) (w : ContentCategory D Sc cutoff N γ.1) : w.obj ⟶ w.obj :=
  weightedContentCapBoundaryCoefficient D Sc cutoff N i γ.1
    (cap_height D cutoff Λ hcutoff i γ hh) w r
    ⟨j, by simpa only [contentCapCount_weightBlock D cutoff i Λ x₁ (hcutoff i) γ] using hj⟩

/-- The represented unit-boundary value, including absent predecessor blocks. -/
def negativeRepresentedValue (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) (w : ContentCategory D Sc cutoff N γ.1) : w.obj ⟶ w.obj :=
  weightedContentUnitBoundaryCoefficient D Sc cutoff N i γ.1
    (unit_height D cutoff Λ hcutoff i γ hh) w
    ⟨j, by simpa only [contentUnitCount_weightBlock D cutoff i Λ x₁ (hcutoff i) γ] using hj⟩ r

attribute [local irreducible] positiveRepresentedValue negativeRepresentedValue

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The represented positive boundary has source difference degree. -/
theorem positiveRepresentedValue_degree (hh : 0 ≤ D.h i x₁)
    (j r : ℕ) (hj : j < (D.h i x₁).toNat) (w : ContentCategory D Sc cutoff N γ.1) :
    positiveRepresentedValue D Sc cutoff N Λ hcutoff i γ hh j r hj w ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word
        (2 * sy.d i * ((r : ℤ) - j)) := by
  unfold positiveRepresentedValue
  exact weightedContentCapBoundaryCoefficient_degree D Sc cutoff N i sy hc γ.1
    (cap_height D cutoff Λ hcutoff i γ hh) w r
      ⟨j, by simpa only [contentCapCount_weightBlock D cutoff i Λ x₁ (hcutoff i) γ] using hj⟩

/-- The represented negative boundary has the same source difference degree. -/
theorem negativeRepresentedValue_degree (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) (w : ContentCategory D Sc cutoff N γ.1) :
    negativeRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r j hj w ∈
      truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word
        (2 * sy.d i * ((r : ℤ) - j)) := by
  unfold negativeRepresentedValue
  exact weightedContentUnitBoundaryCoefficient_degree D Sc cutoff N i sy hc γ.1
    (unit_height D cutoff Λ hcutoff i γ hh) w
      ⟨j, by simpa only [contentUnitCount_weightBlock D cutoff i Λ x₁ (hcutoff i) γ] using hj⟩ r
end ArbitraryOutputs

/-- On supported blocks the literal chosen positive boundary acts by its source value. -/
theorem positive_represented_coordinates (hh : 0 ≤ D.h i x₁)
    (j r : ℕ) (hj : j < (D.h i x₁).toNat)
    (w : ContentCategory D Sc cutoff N δ.1) (b : (M δ).obj w) :
    ((positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh j r).total M δ).total w b =
      (M δ).map (positiveRepresentedValue D Sc cutoff N Λ hcutoff i δ hh j r hj w) b := by
  apply (moduleIsoLinearEquiv (Valueδ) w).injective
  change (Valueδ).hom.total w
      (((positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh j r).total M δ).total w b) =
    (Valueδ).hom.total w
      ((M δ).map (positiveRepresentedValue D Sc cutoff N Λ hcutoff i δ hh j r hj w) b)
  have he := congrArg (fun f => f.total w b)
    (positive_weighted_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ M β hh j hj r)
  simp only [Superfunctor.comp_total, SVec.comp_apply, restriction_map_total] at he
  have hk := weightedContentCapBoundaryValue_evaluate D Sc cutoff N i Pδ δ.1
    (cap_height D cutoff Λ hcutoff i δ hh) w r
    ⟨j, by simpa only [contentCapCount_weightBlock D cutoff i Λ x₁ (hcutoff i) δ] using hj⟩
    ((Valueδ).hom.total w b)
  unfold weightedContentCapBoundaryValue at hk
  change (Valueδ).hom.total w
      (((positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh j r).total M δ).total w b) =
    (capDotRow Tδ (truncatedDot_supernatural D Sc cutoff N i) Pδ r).total w.obj
      (((weightedContentLocalInverseTo D Sc cutoff N i Pδ δ.1
        (cap_height D cutoff Λ hcutoff i δ hh)).g' j).total w ((Valueδ).hom.total w b)) at he
  have hn := even_map_apply (Valueδ).hom
    (contentUnitValueIso_hom_mem D Sc cutoff N δ.1 (M δ))
    (positiveRepresentedValue D Sc cutoff N Λ hcutoff i δ hh j r hj w) b
  unfold positiveRepresentedValue at hn
  have h := he.trans (hk.trans hn.symm)
  convert h using 1
  unfold positiveRepresentedValue
  rfl

section AllOutputs
variable (γ : WeightBlocks D Λ x₁)
local notation "Qγ" => contentInclusion D Sc cutoff N (Subtype.val γ)
local notation "Pγ" => induced Qγ (M γ)
local notation "Valueγ" => contentExtensionUnitIso D Sc cutoff N (Subtype.val γ) (M γ)

/-- The literal chosen negative boundary has its source action on every output block. -/
theorem negative_represented_coordinates (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat)
    (w : ContentCategory D Sc cutoff N γ.1) (b : (M γ).obj w) :
    ((negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j).total M γ).total w b =
      (M γ).map (negativeRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r j hj w) b := by
  apply (moduleIsoLinearEquiv (Valueγ) w).injective
  change (Valueγ).hom.total w
      (((negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j).total M γ).total w b) =
    (Valueγ).hom.total w
      ((M γ).map (negativeRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r j hj w) b)
  have he := congrArg (fun f => f.total w b)
    (negative_weighted_coordinates_all D Sc cutoff N Λ hcutoff i h₁ h₂ M γ hh r j hj)
  simp only [Superfunctor.comp_total, SVec.comp_apply, restriction_map_total] at he
  have hk := weightedContentUnitBoundaryValue_evaluate D Sc cutoff N i Pγ γ.1
    (unit_height D cutoff Λ hcutoff i γ hh) w
    ⟨j, by simpa only [contentUnitCount_weightBlock D cutoff i Λ x₁ (hcutoff i) γ] using hj⟩ r
    ((Valueγ).hom.total w b)
  unfold weightedContentUnitBoundaryValue at hk
  change (Valueγ).hom.total w
      (((negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j).total M γ).total w b) =
    ((weightedContentLocalInverseFrom D Sc cutoff N i Pγ γ.1
      (unit_height D cutoff Λ hcutoff i γ hh)).g' j).total w
      ((unitDotColumn Tδ (truncatedDot_supernatural D Sc cutoff N i) Pγ r).total w.obj
        ((Valueγ).hom.total w b)) at he
  have hn := even_map_apply (Valueγ).hom
    (contentUnitValueIso_hom_mem D Sc cutoff N γ.1 (M γ))
    (negativeRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r j hj w) b
  unfold negativeRepresentedValue at hn
  have h := he.trans (hk.trans hn.symm)
  convert h using 1
  unfold negativeRepresentedValue
  rfl

/-- The negative source action holds on every exact-content module, including absent blocks. -/
theorem negativeContent_represented_coordinates (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    ModuleRepresentedAction (k := k) (C := ContentCategory D Sc cutoff N γ.1)
      (module_centre_action (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j))
      (fun w => negativeRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r j hj w) := by
  exact module_represented_action_of_family_extension
    (k := k) (C := ContentCategory D Sc cutoff N γ.1) (F := ELVWeightProduct D Sc cutoff N Λ x₁)
    (fun F : ELVWeightProduct D Sc cutoff N Λ x₁ => F γ)
    (fun L : ContentModules D Sc cutoff N γ.1 => (WeightCentreBlocks.extension D Sc cutoff N Λ γ).obj L)
    (fun L => WeightCentreBlocks.extension_obj D Sc cutoff N Λ γ L)
    (module_centre_action (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j))
    (fun F => (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j).total F γ)
    (fun w => negativeRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r j hj w)
    (fun F => negativeContent_total D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j F)
    (fun F w b => negative_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ F γ hh r j hj w b)

end AllOutputs

/-- The positive source action holds on every exact-content module at a supported block. -/
theorem positiveContent_represented_coordinates (hh : 0 ≤ D.h i x₁)
    (j r : ℕ) (hj : j < (D.h i x₁).toNat) :
    ModuleRepresentedAction (k := k) (C := ContentCategory D Sc cutoff N δ.1)
      (module_centre_action (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ δ hh j r))
      (fun w => positiveRepresentedValue D Sc cutoff N Λ hcutoff i δ hh j r hj w) := by
  exact module_represented_action_of_family_extension
    (k := k) (C := ContentCategory D Sc cutoff N δ.1) (F := ELVWeightProduct D Sc cutoff N Λ x₁)
    (fun F : ELVWeightProduct D Sc cutoff N Λ x₁ => F δ)
    (fun L : ContentModules D Sc cutoff N δ.1 => (WeightCentreBlocks.extension D Sc cutoff N Λ δ).obj L)
    (fun L => WeightCentreBlocks.extension_obj D Sc cutoff N Λ δ L)
    (module_centre_action (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ δ hh j r))
    (fun F => (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh j r).total F δ)
    (fun w => positiveRepresentedValue D Sc cutoff N Λ hcutoff i δ hh j r hj w)
    (fun F => positiveContent_total D Sc cutoff N Λ hcutoff i h₁ h₂ δ hh j r F)
    (fun F w b => positive_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ F β hh j r hj w b)

variable (γ : WeightBlocks D Λ x₁) (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The reconstructed source coefficient of literal `boundaryPos(j,r)` has difference degree. -/
theorem positiveCoefficient_mem_degree (hh : 0 ≤ D.h i x₁)
    (j r : ℕ) (hj : j < (D.h i x₁).toNat) :
    positiveCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh j r ∈
      contentCoefficientDegree D Sc cutoff N γ.1 sy hc (2 * sy.d i * ((r : ℤ) - j)) := by
  have hpos : 0 < D.h i x₁ := by omega
  obtain ⟨β₁, rfl⟩ := elvWeightPredecessor_of_positive_height D cutoff i Λ h₁ (hcutoff i) hpos γ
  change ModuleCentre.reconstruct D Sc cutoff N (blockSucc D Λ i h₁ β₁).1
    (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ (blockSucc D Λ i h₁ β₁) hh j r) ∈
      contentCoefficientDegree D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 sy hc
        (2 * sy.d i * ((r : ℤ) - j))
  apply ModuleCentre.reconstruct_mem_degree_of_total_evaluation
  intro w
  have he := positiveContent_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ β₁ hh j r hj
    (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w) w (𝟙 w)
  change ((positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂
    (blockSucc D Λ i h₁ β₁) hh j r).total
    (contentRepresentable D Sc cutoff N (blockSucc D Λ i h₁ β₁).1 w)).total w (𝟙 w) = _ at he
  erw [he]
  change (𝟙 w ≫ positiveRepresentedValue D Sc cutoff N Λ hcutoff i
    (blockSucc D Λ i h₁ β₁) hh j r hj w) ∈ _
  rw [Category.id_comp]
  exact positiveRepresentedValue_degree D Sc cutoff N Λ hcutoff i
    (blockSucc D Λ i h₁ β₁) sy hc hh j r hj w

/-- The reconstructed source coefficient of literal `boundaryNeg(r,j)` has difference degree,
including blocks without a predecessor. -/
theorem negativeCoefficient_mem_degree (hh : D.h i x₁ ≤ 0)
    (r j : ℕ) (hj : j < (-D.h i x₁).toNat) :
    negativeCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j ∈
      contentCoefficientDegree D Sc cutoff N γ.1 sy hc (2 * sy.d i * ((r : ℤ) - j)) := by
  change ModuleCentre.reconstruct D Sc cutoff N γ.1
    (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j) ∈
      contentCoefficientDegree D Sc cutoff N γ.1 sy hc (2 * sy.d i * ((r : ℤ) - j))
  apply ModuleCentre.reconstruct_mem_degree_of_total_evaluation
  intro w
  have he := negativeContent_represented_coordinates D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j hj
    (contentRepresentable D Sc cutoff N γ.1 w) w (𝟙 w)
  change ((negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ γ hh r j).total
    (contentRepresentable D Sc cutoff N γ.1 w)).total w (𝟙 w) = _ at he
  erw [he]
  change (𝟙 w ≫ negativeRepresentedValue D Sc cutoff N Λ hcutoff i γ hh r j hj w) ∈ _
  rw [Category.id_comp]
  exact negativeRepresentedValue_degree D Sc cutoff N Λ hcutoff i γ sy hc hh r j hj w

end OddMath.QuiverHecke.ELVOld.ReservoirBoundaries
end

end

section

/-! # The chosen off-window boundaries in the content coefficient ideal

SwappedHomInversion §4, condition (J): a finite inverse slot j contracted
with a dotted row or column r > j has positive source coefficient degree.
Its exact-content action lies in level one of the jointly nilpotent ideal,
including arbitrary surrounding morphisms and native Hom-sector charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ReservoirBoundaries
open CyclotomicAction SwappedAssembly
universe u
local instance boundaryIdealHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (Λ : X) (hcutoff : ∀ i, (cutoff i : ℤ) = D.h i Λ)
  (i : I) {x₀ x₁ x₂ : X} (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₁) (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The positive chosen finite-window boundary has its difference degree. -/
theorem positiveContent_mem_coeffGrading (hh : 0 ≤ D.h i x₁) (j r : ℕ)
    (hj : j < (D.h i x₁).toNat) :
    positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh j r ∈
      (contentModuleCoeffGrading D Sc cutoff N β.1 sy hc).deg
        (2 * sy.d i * ((r : ℤ) - j)) := by
  refine ⟨positiveCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh j r,
    positiveCoefficient_mem_degree D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh j r hj, ?_⟩
  exact ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _

/-- The negative chosen finite-window boundary has its difference degree. -/
theorem negativeContent_mem_coeffGrading (hh : D.h i x₁ ≤ 0) (j r : ℕ)
    (hj : j < (-D.h i x₁).toNat) :
    negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r j ∈
      (contentModuleCoeffGrading D Sc cutoff N β.1 sy hc).deg
        (2 * sy.d i * ((r : ℤ) - j)) := by
  refine ⟨negativeCoefficient D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r j,
    negativeCoefficient_mem_degree D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh r j hj, ?_⟩
  exact ModuleCentre.realize_reconstruct D Sc cutoff N β.1 _

variable [Finite I] (T : PiSCat.{u,u,u + 1} k)

/-- Arbitrary transformations can surround the positive off-window coefficient. -/
theorem positiveContent_sandwich_mem (hh : 0 ≤ D.h i x₁) (j r : ℕ)
    (hj : j < (D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1} (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (positiveContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh j r) ≫ b) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGrading D Sc cutoff N β.1 sy hc)
    (m := 2 * sy.d i * ((r : ℤ) - j))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r : ℤ) - j := by omega
    have hd : (0 : ℤ) < 2 * sy.d i * ((r : ℤ) - j) := by positivity
    omega
  · exact positiveContent_mem_coeffGrading D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh j r hj

/-- The projected whole-weight positive off-window action lies in the content ideal. -/
theorem positiveAction_evaluate_mem (hh : 0 ≤ D.h i x₁) (j r : ℕ)
    (hj : j < (D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z (positive D Sc cutoff N Λ hcutoff i h₁ h₂ hh j r) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact positiveContent_sandwich_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc T hh j r hj hjr
    (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight b (elvBlockEval D Sc cutoff N Λ β))

/-- Arbitrary transformations can surround the negative off-window coefficient. -/
theorem negativeContent_sandwich_mem (hh : D.h i x₁ ≤ 0) (j r : ℕ)
    (hj : j < (-D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ contentModuleTarget D Sc cutoff N β.1} (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (a ≫ ProbeWindow.postCoeff Z
        (negativeContent D Sc cutoff N Λ hcutoff i h₁ h₂ β hh r j) ≫ b) := by
  apply ProbeWindow.comp_postCoeff_comp_mem
    (Gr := contentModuleCoeffGrading D Sc cutoff N β.1 sy hc)
    (m := 2 * sy.d i * ((r : ℤ) - j))
  · have hp := sy.pos i
    have hr : (0 : ℤ) < (r : ℤ) - j := by omega
    have hd : (0 : ℤ) < 2 * sy.d i * ((r : ℤ) - j) := by positivity
    omega
  · exact negativeContent_mem_coeffGrading D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc hh j r hj

/-- The projected whole-weight negative off-window action lies in the content ideal. -/
theorem negativeAction_evaluate_mem (hh : D.h i x₁ ≤ 0) (j r : ℕ)
    (hj : j < (-D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : T ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc T).mem 1
      (Superfunctor.whiskerRight
        (a ≫ ProbeWindow.postCoeff Z (negative D Sc cutoff N Λ hcutoff i h₁ h₂ hh r j) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  rw [Superfunctor.comp_whiskerRight, Superfunctor.comp_whiskerRight,
    WeightCentreBlocks.postCoeff_evaluate]
  exact negativeContent_sandwich_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc T hh j r hj hjr
    (Superfunctor.whiskerRight a (elvBlockEval D Sc cutoff N Λ β))
    (Superfunctor.whiskerRight b (elvBlockEval D Sc cutoff N Λ β))

local notation "W" => elvRouquierFamily D Sc cutoff N Λ hcutoff

/-- The literal native positive off-window contraction has the same ideal membership. -/
theorem positiveBoundary_evaluate_mem
    (TF : X → PiSCat.{u,u,u + 1} k) (betaP : I →₀ ℕ) (muP : X)
    (hh : 0 ≤ D.h i x₁) (j r : ℕ) (hj : j < (D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc (TF (-muP))).mem 1
      (Superfunctor.whiskerRight (a ≫ ((SKM.homContentPostInvPos TF W i betaP muP h₁ h₂ hh Z).g' j ≫
          SKM.homContentPostCap TF W i betaP muP h₁ r Z) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCapInverse_boundary TF W i betaP muP h₁ h₂ hh Z j r]
  simpa only [positive] using
    positiveAction_evaluate_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc (TF (-muP)) hh j r hj hjr a b

/-- The literal native negative off-window contraction has the same ideal membership. -/
theorem negativeBoundary_evaluate_mem
    (TF : X → PiSCat.{u,u,u + 1} k) (betaP : I →₀ ℕ) (muP : X)
    (hh : D.h i x₁ ≤ 0) (j r : ℕ) (hj : j < (-D.h i x₁).toNat) (hjr : j < r)
    {V Z Y : TF (-muP) ⟶ elvWeightSpace D Sc cutoff N Λ x₁} (a : V ⟶ Z) (b : Z ⟶ Y) :
    (contentModuleCoefficientIdeal D Sc cutoff N β.1 sy hc (TF (-muP))).mem 1
      (Superfunctor.whiskerRight (a ≫ (SKM.homContentPostCup TF W i betaP muP h₂ r Z ≫
          (SKM.homContentPostInvNeg TF W i betaP muP h₁ h₂ hh Z).g' j) ≫ b)
        (elvBlockEval D Sc cutoff N Λ β)) := by
  erw [postCupInverse_boundary TF W i betaP muP h₁ h₂ hh Z r j]
  simpa only [negative] using
    negativeAction_evaluate_mem D Sc cutoff N Λ hcutoff i h₁ h₂ β sy hc (TF (-muP)) hh j r hj hjr a b

end OddMath.QuiverHecke.ELVOld.ReservoirBoundaries
end

end

section

/-! # Actual reservoir words as the chosen E contexts

SwappedVacuumCoordinates §§2–6: compare the unchanged reservoir word
at arbitrary intermediate formal content with the prescribed context
functor, using the proved original-weight endpoint and reversed labels.
No support or boundary vanishing property of arbitrary Hom objects is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.ReservoirContexts
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (cutoff : I → ℕ) (L : I × ℕ → ℕ) (Λ : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "W" => elvRouquierData D Sc cutoff N Λ

omit [Fintype I] in
private theorem context_weight_append (x : X) (η : List I) (i : I) :
    PowerWordWeightContexts.contextWeight D x (η ++ [i]) =
      PowerWordWeightContexts.contextWeight D x η + D.α i := by
  induction η generalizing x with
  | nil => rfl
  | cons j η ih => exact ih (x + D.α j)

omit [Fintype I] in
private theorem edge (i : I) (c : I →₀ ℕ) (hc : 1 ≤ c i) :
    ReservoirWord.weight D Λ (c - Finsupp.single i 1) + D.α i = ReservoirWord.weight D Λ c := by
  simp only [ReservoirWord.weight]
  rw [add_assoc, contentWeight_sub_single hc]

private theorem pre_heq {x₀ x y y' : X} (hy : y = y')
    {F : elvWeightSpace D Sc cutoff N Λ x ⟶ elvWeightSpace D Sc cutoff N Λ y}
    {F' : elvWeightSpace D Sc cutoff N Λ x ⟶ elvWeightSpace D Sc cutoff N Λ y'}
    (K : elvWeightSpace D Sc cutoff N Λ x₀ ⟶ elvWeightSpace D Sc cutoff N Λ x)
    (hF : HEq F F') : HEq (K ≫ F) (K ≫ F') := by
  cases hy
  cases hF
  rfl

private theorem postE_heq (i : I) {x₀ x y x' y' : X} (hx : x = x') (hy : y = y')
    (h : x + D.α i = y) (h' : x' + D.α i = y')
    {F : elvWeightSpace D Sc cutoff N Λ x₀ ⟶ elvWeightSpace D Sc cutoff N Λ x}
    {F' : elvWeightSpace D Sc cutoff N Λ x₀ ⟶ elvWeightSpace D Sc cutoff N Λ x'}
    (hF : HEq F F') : HEq (F ≫ (W).E i h) (F' ≫ (W).E i h') := by
  cases hx
  cases hy
  cases hF
  rfl

private theorem context_append_heq (x : X) (η : List I) (i : I) :
    HEq (TensorHomContexts.context D Sc cutoff L Λ x (η ++ [i]))
      (TensorHomContexts.context D Sc cutoff L Λ x η ≫
        (W).E i (rfl : PowerWordWeightContexts.contextWeight D x η + D.α i =
          PowerWordWeightContexts.contextWeight D x η + D.α i)) := by
  induction η generalizing x with
  | nil => rfl
  | cons j η ih =>
    exact pre_heq D Sc cutoff L Λ (context_weight_append D (x + D.α j) η i)
      ((W).E j (rfl : x + D.α j = x + D.α j)) (ih (x + D.α j))

private theorem context_word_heq (x : X) {η θ : List I} (h : η = θ) :
    HEq (TensorHomContexts.context D Sc cutoff L Λ x η)
      (TensorHomContexts.context D Sc cutoff L Λ x θ) := by
  subst θ
  rfl

omit [Fintype I] in
/-- The endpoint weight follows the actual reversed colour context,
including a nonzero intermediate formal starting content. -/
theorem word_weight {l : List (SKM.Col I X)} {c d : I →₀ ℕ}
    (p : SPath l (0,c) (0,d)) (hl : ∀ a ∈ l, a.l.1 = true) :
    ReservoirWord.weight D Λ c = PowerWordWeightContexts.contextWeight D
      (ReservoirWord.weight D Λ d) ((l.map (fun a => a.l.2)).reverse) := by
  induction l generalizing c with
  | nil => cases p; rfl
  | cons a l ih =>
    cases p with
    | cons a side s hv p =>
      have ha := hl a List.mem_cons_self
      have ht : ∀ b ∈ l, b.l.1 = true := fun b hb => hl b (List.mem_cons_of_mem _ hb)
      rcases a with ⟨⟨b,i⟩,r⟩
      cases b with
      | false => cases ha
      | true =>
        have hs := SPath.side_eq_false_of_upward_probe_zero i side p ht rfl
        subst side
        have hy := (edge D Λ i c hv).symm.trans ((congrArg (fun x => x + D.α i) (ih p ht)).trans
          (context_weight_append D (ReservoirWord.weight D Λ d) ((l.map (fun a => a.l.2)).reverse) i).symm)
        simpa only [List.map_cons, List.reverse_cons] using hy

/-- The whole given reservoir word and the chosen E-context functor
agree after changing only their proved original-weight endpoint. -/
theorem word_heq {l : List (SKM.Col I X)} {c d : I →₀ ℕ}
    (p : SPath l (0,c) (0,d)) (hl : ∀ a ∈ l, a.l.1 = true) :
    HEq (ReservoirWord.word (W) Λ p hl)
      (TensorHomContexts.context D Sc cutoff L Λ (ReservoirWord.weight D Λ d)
        ((l.map (fun a => a.l.2)).reverse)) := by
  induction l generalizing c with
  | nil => cases p; rw [ReservoirWord.word_nil]; rfl
  | cons a l ih =>
    cases p with
    | cons a side s hv p =>
      have ha := hl a List.mem_cons_self
      have ht : ∀ b ∈ l, b.l.1 = true := fun b hb => hl b (List.mem_cons_of_mem _ hb)
      rcases a with ⟨⟨b,i⟩,r⟩
      cases b with
      | false => cases ha
      | true =>
        have hs := SPath.side_eq_false_of_upward_probe_zero i side p ht rfl
        subst side
        change SPath l (0,c - Finsupp.single i 1) (0,d) at p
        have hci : 1 ≤ c i := hv
        have hx := word_weight D Λ p ht
        have hy := (edge D Λ i c hci).symm.trans (congrArg (fun x => x + D.α i) hx)
        have hpost := postE_heq D Sc cutoff L Λ i hx hy (edge D Λ i c hci) rfl (ih p ht)
        have happ := context_append_heq D Sc cutoff L Λ (ReservoirWord.weight D Λ d)
          ((l.map (fun a => a.l.2)).reverse) i
        have hwords : ((l.map (fun a => a.l.2)).reverse) ++ [i] =
            (((⟨(true,i),r⟩ :: l).map (fun a => a.l.2)).reverse) := by
          rw [List.map_cons, List.reverse_cons]
        have hlist := context_word_heq D Sc cutoff L Λ (ReservoirWord.weight D Λ d) hwords
        exact (heq_of_eq (ReservoirWord.word_cons (W) Λ i r hci p ht)).trans
          (hpost.trans (happ.symm.trans hlist))

private def atWeight {x y y' : X} (h : y = y')
    (F : elvWeightSpace D Sc cutoff N Λ x ⟶ elvWeightSpace D Sc cutoff N Λ y) :
    elvWeightSpace D Sc cutoff N Λ x ⟶ elvWeightSpace D Sc cutoff N Λ y' := h ▸ F

private theorem atWeight_heq {x y y' : X} (h : y = y')
    (F : elvWeightSpace D Sc cutoff N Λ x ⟶ elvWeightSpace D Sc cutoff N Λ y) :
    HEq (atWeight D Sc cutoff L Λ h F) F := by cases h; rfl

/-- The actual outer reservoir word at its proved context endpoint. -/
def wordAt {l : List (SKM.Col I X)} {c d : I →₀ ℕ}
    (p : SPath l (0,c) (0,d)) (hl : ∀ a ∈ l, a.l.1 = true) :
    elvWeightSpace D Sc cutoff N Λ (ReservoirWord.weight D Λ d) ⟶
      elvWeightSpace D Sc cutoff N Λ (PowerWordWeightContexts.contextWeight D
        (ReservoirWord.weight D Λ d) ((l.map (fun a => a.l.2)).reverse)) :=
  atWeight D Sc cutoff L Λ (word_weight D Λ p hl) (ReservoirWord.word (W) Λ p hl)

end OddMath.QuiverHecke.ELVOld.ReservoirContexts
end

end
