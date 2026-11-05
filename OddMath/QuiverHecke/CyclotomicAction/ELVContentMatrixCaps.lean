import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixRows

/-! # Prescribed cap rows under the chosen content source chart

DeformedMatrixComparison (4), (5): the preceding E/F chart retains the
literal ordinary counit and lower dot powers before canonical target
parity coordinates. No cap compatibility premise is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
private theorem coendComp_ext
    {k C A V W Z : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    (f : Obj J M w →ₗ[k] V) (g : V →ₗ[k] Z)
    (h : Obj J M w →ₗ[k] W) (l : W →ₗ[k] Z)
    (hh : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      g (f (tensor J M s a b)) = l (h (tensor J M s a b))) : g ∘ₗ f = l ∘ₗ h := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (BalancedInduction.relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact hh s a b

private theorem compose_intertwine
    {k V W Z : Type u} [CommRing k] [AddCommMonoid V] [Module k V]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (C₁ : V →ₗ[k] W) (C₂ : W →ₗ[k] Z)
    (f : Module.End k V) (g : Module.End k W) (h : Module.End k Z)
    (h₁ : C₁ ∘ₗ f = g ∘ₗ C₁) (h₂ : C₂ ∘ₗ g = h ∘ₗ C₂) :
    (C₂ ∘ₗ C₁) ∘ₗ f = h ∘ₗ (C₂ ∘ₗ C₁) := by
  apply LinearMap.ext
  intro x
  exact (congrArg C₂ (LinearMap.congr_fun h₁ x)).trans (LinearMap.congr_fun h₂ (C₁ x))

namespace BalancedInduction
private theorem capDotLinear_intertwine
    {k C A W Z : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [AddCommMonoid W] [Module k W] [AddCommMonoid Z] [Module k Z]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (N : Superfunctor k A (SVec k)) (w : A)
    (L : Obj J ((restriction J).obj N).toFunctor w →ₗ[k] W) (g : Module.End k W)
    (V : N.obj w →ₗ[k] Z) (c : W →ₗ[k] Z)
    (hd : L ∘ₗ transformLinear hα ((restriction J).obj N) w = g ∘ₗ L)
    (hc : V ∘ₗ restrictionCounitLinear J N w = c ∘ₗ L) (n : ℕ)
    (x : Obj J ((restriction J).obj N).toFunctor w) :
    V (capDotLinear J hα N n w x) = c ((g ^ n) (L x)) := by
  let f : Module.End k (Obj J ((restriction J).obj N).toFunctor w) :=
    transformLinear hα ((restriction J).obj N) w
  have h₀ := LinearMap.congr_fun hc ((f ^ n) x)
  have hp := intertwine_pow_apply L f g (fun y => LinearMap.congr_fun hd y) n x
  exact h₀.trans (congrArg c hp)

private theorem capDotLinear_apply_power
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (N : Superfunctor k A (SVec k)) (n : ℕ) (w : A)
    (x : Obj J ((restriction J).obj N).toFunctor w) :
    capDotLinear J hα N n w x = restrictionCounitLinear J N w
      (((transformLinear hα ((restriction J).obj N) w :
        Module.End k (Obj J ((restriction J).obj N).toFunctor w)) ^ n) x) := rfl
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "Q₀" => oldContentInclusion D Sc cutoff ν
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i

/-- The genuine selected source and value charts carry the independently
given content counit to the given old ordinary counit. -/
theorem oldContentEFLinearEquiv_counit
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentValueLinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      restrictionCounitLinear J₀ N t =
    restrictionCounitLinear J (induced Q₁ N) t.obj ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  apply coendComp_ext J₀ ((restriction J₀).obj N).toFunctor
  intro s a b
  have hc := restrictionCounitLinear_tensor J₀ N s t a b
  have hl := congrArg (oldContentValueLinearEquiv D Sc cutoff ν i N t) hc
  have hv := oldContentValueLinearEquiv_apply D Sc cutoff ν i N t (N.map a b)
  have hLeft := hl.trans hv
  have he := oldContentEFRestrictionLinear_tensor D Sc cutoff ν i N s t a b
  have hStep := congrArg (restrictionCounitLinear J (induced Q₁ N) t.obj) he
  have hOld := restrictionCounitLinear_tensor J (induced Q₁ N) s.obj t.obj a
    (tensor Q₁ N.toFunctor ((J₀).obj s) (𝟙 ((J).obj s.obj)) b)
  have hu := LinearMap.congr_fun (unit_naturality Q₁ N.toFunctor a) b
  set_option backward.dsimp.instances true in
    dsimp only [restriction, Superfunctor.comp] at hStep hOld
  have hRight := hStep.trans hOld
  have hUnit : (induced Q₁ N).map a
      (tensor Q₁ N.toFunctor ((J₀).obj s) (𝟙 ((J).obj s.obj)) b) =
      tensor Q₁ N.toFunctor t (𝟙 t.obj) (N.map a b) := hu
  have hWhole := hLeft.trans (hUnit.symm.trans hRight.symm)
  rw [oldContentEFLinearEquiv_hom]
  set_option backward.dsimp.instances true in
    dsimp only [restriction, Superfunctor.comp] at hWhole ⊢
  exact hWhole

/-- The same selected preceding E/F source chart intertwines the literal
lower dot, including its complete coefficient twist. -/
theorem oldContentEFLinearEquiv_dot
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      transformLinear (oldContentAppendDot_supernatural D Sc cutoff ν i)
        ((restriction J₀).obj N) t =
    inductionDot D Sc cutoff i ((restriction J).obj (induced Q₁ N)) t.obj ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  let C₁ := oldContentAppendRestrictionLinear D Sc cutoff ν i ((restriction J₀).obj N) t
  let C₂ := mapComponent J (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom 0 t.obj
  have h₁ := oldContentAppendRestrictionIso_dot D Sc cutoff ν i ((restriction J₀).obj N) t
  have h₂ := transform_mapComponent (oldAppendDot_supernatural D Sc cutoff i)
    (induced Q₀ ((restriction J₀).obj N))
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom 0 t.obj
  simp only [mul_zero, sign_zero, one_smul] at h₂
  dsimp only [inductionDot] at h₁ ⊢
  have hcomp := compose_intertwine _ _ _ _ _ h₁ h₂.symm
  have hfactor : (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap = C₂ ∘ₗ C₁ := by
    apply LinearMap.ext
    intro x
    rw [oldContentEFLinearEquiv_hom]
    dsimp only [C₁, C₂, LinearMap.comp_apply]
    exact oldContentEFRestrictionLinear_apply D Sc cutoff ν i N t x
  rw [hfactor]
  exact hcomp

/-- Every prescribed dot/counit row is carried by the genuine selected
preceding E/F and value charts to the identical old cap row. -/
theorem oldContentEFLinearEquiv_capDot
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) (n : ℕ)
    (x : Obj J₀ ((restriction J₀).obj N).toFunctor t) :
    oldContentValueLinearEquiv D Sc cutoff ν i N t
      (capDotLinear J₀ (oldContentAppendDot_supernatural D Sc cutoff ν i) N n t x) =
    capDotLinear J (oldAppendDot_supernatural D Sc cutoff i) (induced Q₁ N) n t.obj
      (oldContentEFLinearEquiv D Sc cutoff ν i N t x) := by
  have hd := oldContentEFLinearEquiv_dot D Sc cutoff ν i N t
  have hc := oldContentEFLinearEquiv_counit D Sc cutoff ν i N t
  have hp := BalancedInduction.capDotLinear_intertwine J₀
    (oldContentAppendDot_supernatural D Sc cutoff ν i) N t _ _ _ _ hd hc n x
  have ht := BalancedInduction.capDotLinear_apply_power J
    (oldAppendDot_supernatural D Sc cutoff i) (induced Q₁ N) n t.obj
    (oldContentEFLinearEquiv D Sc cutoff ν i N t x)
  dsimp only [inductionDot] at hp
  exact hp.trans ht.symm

end OddMath.QuiverHecke.ELVOld
