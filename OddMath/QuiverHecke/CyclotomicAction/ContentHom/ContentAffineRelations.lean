import OddMath.QuiverHecke.CyclotomicAction.ContentHom.ContentHomSupport
import OddMath.QuiverHecke.CyclotomicAction.ContentMatrix.ContentMissingColourMatrix
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMatrix.InductionGridMatrixFamilies
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts.ProbeUpperCharts

/-!
# Content hom

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Affine relations in the untruncated old content quotient

The local action of BE (1.13)–(1.14) requires the literal positive old equal crossing to be square-zero
and to satisfy both signed dot slides. All relations descend directly
from affine relations through the full-coefficient old quotient. The
stored content targets are cons lists, while underlying words append
on the right. These are the coefficient inputs for the probe local action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem oldDot_affine (i : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i s =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [i]) s.word.length)) := by
  rw [oldAppendDotComponent_eq, appendMovingPower, pow_one]

private theorem oldLowerDot_affine (i : I) (s : OldCategory D Sc cutoff) :
    (append D Sc cutoff i).map (oldAppendDotComponent D Sc cutoff i s) =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [i] ++ [i]) s.word.length)) := by
  rw [oldDot_affine]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [i]) (s.word ++ [i] ++ [i])).mkQ
    (rightContext D Sc cutoff [i] (s.word ++ [i]) (s.word ++ [i])
      (affineUnit D Sc cutoff (s.word ++ [i]) (s.word ++ [i])
        (dotE D Sc (s.word ++ [i]) s.word.length))) = _
  rw [rightContext_affineUnit]
  change (ideal D Sc cutoff (s.word ++ [i] ++ [i]) (s.word ++ [i] ++ [i])).mkQ
    (affineUnit D Sc cutoff (s.word ++ [i] ++ [i]) (s.word ++ [i] ++ [i])
      (dotE D Sc (s.word ++ [i]) s.word.length ▷ (pres D Sc).obj (ob D [i]))) = _
  rw [dotE_whiskerRight D Sc (s.word ++ [i]) [i] s.word.length (by simp)]

private theorem oldUpperDot_affine (i : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i ((append D Sc cutoff i).obj s) =
      (ideal D Sc cutoff _ _).mkQ (affineUnit D Sc cutoff _ _
        (dotE D Sc (s.word ++ [i] ++ [i]) (s.word.length + 1))) := by
  simpa only [append, List.length_append, List.length_singleton] using
    oldDot_affine D Sc cutoff i ((append D Sc cutoff i).obj s)

private theorem affineCrossLast_square (v : List I) (i : I) :
    crossLast D Sc v i i ≫ crossLast D Sc v i i = 0 := by
  have he := crossE_mul_crossE D Sc (w := v ++ [i] ++ [i]) v [] i
    (j := v.length) rfl (by simp [List.append_assoc])
  have hc : crossE D Sc (v ++ [i] ++ [i]) v.length = crossLast D Sc v i i := by
    unfold crossE
    rw [genE_eq D Sc (by simpa using sChain_crossAt v [] i i)]
    rfl
  simpa only [hc, End.mul_def] using he

private theorem oldCross_square (i : I) (s : OldCategory D Sc cutoff) :
    equalCrossComponent D Sc cutoff i s ≫ equalCrossComponent D Sc cutoff i s = 0 := by
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
    ((ideal D Sc cutoff _ _).mkQ _) = 0
  rw [oldComp_mk, ← affineUnit_comp, affineCrossLast_square, map_zero, map_zero]

private theorem affine_slideLeft (v : List I) (i : I) :
    affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i] ++ [i]) v.length) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc v i i) -
      sign k (D.parity i * D.parity i) •
        (affineUnit D Sc cutoff _ _ (crossLast D Sc v i i) ≫
          affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i] ++ [i]) (v.length + 1))) = 𝟙 _ := by
  have h := congrArg (affineUnit D Sc cutoff _ _) (dotE_comp_crossLast_self D Sc (i := i) v)
  rw [map_add, map_smul, affineUnit_comp, affineUnit_comp, affineUnit_id,
    ← sign_eq_zsign] at h
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

private theorem affine_slideRight (v : List I) (i : I) :
    affineUnit D Sc cutoff _ _ (crossLast D Sc v i i) ≫
        affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i] ++ [i]) v.length) -
      sign k (D.parity i * D.parity i) •
        (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i] ++ [i]) (v.length + 1)) ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc v i i)) = 𝟙 _ := by
  have h := congrArg (affineUnit D Sc cutoff _ _) (crossLast_comp_dotE_self D Sc (i := i) v)
  rw [map_add, map_smul, affineUnit_comp, affineUnit_comp, affineUnit_id,
    ← sign_eq_zsign] at h
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

private theorem oldCross_slideLeft (i : I) (s : OldCategory D Sc cutoff) :
    (show End (((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s) from
      (append D Sc cutoff i).map (oldAppendDotComponent D Sc cutoff i s)) ≫
        equalCrossComponent D Sc cutoff i s -
      sign k (D.parity i * D.parity i) •
        (equalCrossComponent D Sc cutoff i s ≫
          (show End (((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s) from
            oldAppendDotComponent D Sc cutoff i ((append D Sc cutoff i).obj s))) = 𝟙 _ := by
  rw [oldLowerDot_affine, oldUpperDot_affine]
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) - sign k (D.parity i * D.parity i) •
    oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) = (ideal D Sc cutoff _ _).mkQ (𝟙 _)
  rw [oldComp_mk, oldComp_mk, ← map_smul, ← map_sub]
  exact congrArg (ideal D Sc cutoff _ _).mkQ (affine_slideLeft D Sc cutoff s.word i)

private theorem oldCross_slideRight (i : I) (s : OldCategory D Sc cutoff) :
    equalCrossComponent D Sc cutoff i s ≫
        (show End (((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s) from
          (append D Sc cutoff i).map (oldAppendDotComponent D Sc cutoff i s)) -
      sign k (D.parity i * D.parity i) •
        ((show End (((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s) from
          oldAppendDotComponent D Sc cutoff i ((append D Sc cutoff i).obj s)) ≫
          equalCrossComponent D Sc cutoff i s) = 𝟙 _ := by
  rw [oldLowerDot_affine, oldUpperDot_affine]
  change oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) - sign k (D.parity i * D.parity i) •
    oldComp D Sc cutoff _ _ _ ((ideal D Sc cutoff _ _).mkQ _)
      ((ideal D Sc cutoff _ _).mkQ _) = (ideal D Sc cutoff _ _).mkQ (𝟙 _)
  rw [oldComp_mk, oldComp_mk, ← map_smul, ← map_sub]
  exact congrArg (ideal D Sc cutoff _ _).mkQ (affine_slideRight D Sc cutoff s.word i)

variable (ν : List I) (i : I)
local notation "J" => oldContentAppend D Sc cutoff ν i
local notation "K" => oldContentAppend D Sc cutoff (i :: ν) i
variable (s : OldContentCategory D Sc cutoff ν)
local notation "γ" => oldContentEqualCross D Sc cutoff ν i s
/-- The literal positive last equal crossing is square-zero in the old content quotient. -/
theorem oldContentEqualCross_square : γ ≫ γ = 0 := oldCross_square D Sc cutoff i s.obj

/-- The first signed affine slide uses the literal two selected append dots. -/
theorem oldContentEqualCross_slideLeft :
    (show End (CategoryTheory.Functor.obj (J ⋙ K) s) from
      CategoryTheory.Functor.map K (oldContentAppendDot D Sc cutoff ν i s)) ≫ γ -
      koszulSign (D.parity i) (D.parity i) •
        (γ ≫ (show End (CategoryTheory.Functor.obj (J ⋙ K) s) from
          oldContentAppendDot D Sc cutoff (i :: ν) i (CategoryTheory.Functor.obj J s))) = 𝟙 _ := by
  rw [koszulSign_smul (R := k)]
  exact oldCross_slideLeft D Sc cutoff i s.obj

/-- The second signed affine slide retains the same positive crossing and dots. -/
theorem oldContentEqualCross_slideRight :
    γ ≫ (show End (CategoryTheory.Functor.obj (J ⋙ K) s) from
      CategoryTheory.Functor.map K (oldContentAppendDot D Sc cutoff ν i s)) -
      koszulSign (D.parity i) (D.parity i) •
        ((show End (CategoryTheory.Functor.obj (J ⋙ K) s) from
          oldContentAppendDot D Sc cutoff (i :: ν) i (CategoryTheory.Functor.obj J s)) ≫ γ) = 𝟙 _ := by
  rw [koszulSign_smul (R := k)]
  exact oldCross_slideRight D Sc cutoff i s.obj

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The prescribed mate on entire chosen content coends

DeformedMatrixComparison (4), (5), principal matrix field. Genuine selected
E/F charts carry the independently given content cup-crossing-cap to the
literal old matrix mate on every coend vector, before finite parity shifts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor BalancedInduction
universe u
namespace BalancedInduction
private def mateLinear
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    (M : Superfunctor k C (SVec k))
    (f : induced A ((restriction A).obj M) ⟶ (restriction A).obj (induced A M)) (t : C) :
    Obj A ((restriction A).obj M).toFunctor t →ₗ[k] Obj A M.toFunctor (A.obj t) := f.total t

private theorem mateLinear_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    (M : Superfunctor k C (SVec k))
    (f : induced A ((restriction A).obj M) ⟶ (restriction A).obj (induced A M)) (t : C)
    (x : Obj A ((restriction A).obj M).toFunctor t) :
    mateLinear A M f t x = f.total t x := rfl

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
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact hh s a b
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i

/-- The prescribed old mate on the literal raw coend carriers. -/
def oldMatrixMateLinear
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) :
    Obj J ((restriction J).obj M).toFunctor t →ₗ[k] Obj J M.toFunctor ((J).obj t) :=
  BalancedInduction.mateLinear J M (matrixMateComponent D Sc cutoff i M) t

/-- The raw map evaluates to the same prescribed module component. -/
theorem oldMatrixMateLinear_apply
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (x : Obj J ((restriction J).obj M).toFunctor t) :
    oldMatrixMateLinear D Sc cutoff i M t x = (matrixMateComponent D Sc cutoff i M).total t x :=
  BalancedInduction.mateLinear_apply J M (matrixMateComponent D Sc cutoff i M) t x

/-- The prescribed mate forms a whole linear-map square under the chosen charts. -/
theorem oldContentMatrixCharts_mate_comp
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      orderedGridMateLinear J₀ J₁ (oldContentEqualCross_supernatural D Sc cutoff ν i) N t =
    oldMatrixMateLinear D Sc cutoff i (induced Q₁ N) t.obj ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  apply BalancedInduction.coendComp_ext J₀ ((restriction J₀).obj N).toFunctor
  intro s a b
  have h := oldContentMatrixCharts_mate_tensor D Sc cutoff ν i N s t a b
  have hm := oldMatrixMateLinear_apply D Sc cutoff i (induced Q₁ N) t.obj
    ((oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap
      (tensor J₀ ((restriction J₀).obj N).toFunctor s a b))
  exact h.trans hm.symm

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Prescribed cap rows under the chosen content source chart

DeformedMatrixComparison (4), (5): the preceding E/F chart retains the
literal ordinary counit and lower dot powers before canonical target
parity coordinates. No cap compatibility premise is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Chosen content coordinates for finite unit and cap families

Brundan--Ellis (1.13)--(1.14), DeformedMatrixComparison (4), (5):
the canonical parity coordinates conjugate the selected E/F and value
linear equivalences. These are genuine whole finite-family equivalences,
independently of any inverse-matrix or chart-evenness premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i
local instance contentGridCoordinatesPi : PiSupercategory k
    (Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) := supermodulePiSupercategory
local instance oldGridCoordinatesPi : PiSupercategory k
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) := supermodulePiSupercategory
variable (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
  (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν))
local notation "M" => induced Q₁ N

/-- Every unit-family coordinate uses its selected plain chart and the
existing canonical source and target parity coordinates. -/
def oldContentUnitSlotEquiv (a : Option (Fin m)) :
    (gridUnitMatrixFamily J₀ (D.parity i) N m a).obj t ≃ₗ[k]
      (unitMatrixFamily D Sc cutoff i M m a).obj t.obj := by
  cases a with
  | none =>
    dsimp only [gridUnitMatrixFamily, unitMatrixFamily]
    exact shiftedModuleValueLinearEquiv
      (induced J₀ ((restriction J₀).obj N)) (induced J ((restriction J).obj M))
      t t.obj (oldContentEFLinearEquiv D Sc cutoff ν i N t) (D.parity i)
  | some r =>
    dsimp only [gridUnitMatrixFamily, unitMatrixFamily]
    exact shiftedModuleValueLinearEquiv N M t t.obj
      (oldContentValueLinearEquiv D Sc cutoff ν i N t) (r.val • D.parity i)

/-- Every cap-family coordinate retains its selected F/E or value chart. -/
def oldContentCapSlotEquiv (a : Option (Fin m)) :
    (gridCapMatrixFamily J₁ (D.parity i) N m a).obj t ≃ₗ[k]
      (capMatrixFamily D Sc cutoff i M m a).obj t.obj := by
  cases a with
  | none =>
    dsimp only [gridCapMatrixFamily, capMatrixFamily]
    exact shiftedModuleValueLinearEquiv
      ((restriction J₁).obj (induced J₁ N)) ((restriction J).obj (induced J M))
      t t.obj (oldContentFELinearEquiv D Sc cutoff ν i N t) (D.parity i)
  | some r =>
    dsimp only [gridCapMatrixFamily, capMatrixFamily]
    exact shiftedModuleValueLinearEquiv N M t t.obj
      (oldContentValueLinearEquiv D Sc cutoff ν i N t) (r.val • D.parity i)

/-- The whole finite unit source comparison is a genuine coordinate product. -/
def oldContentUnitFamilyEquiv :
    gridUnitMatrixSourceSpace J₀ (D.parity i) N m t ≃ₗ[k]
      unitMatrixSourceSpace D Sc cutoff i M m t.obj :=
  LinearEquiv.piCongrRight (oldContentUnitSlotEquiv D Sc cutoff ν i N m t)

/-- The whole finite cap target comparison is a genuine coordinate product. -/
def oldContentCapFamilyEquiv :
    gridCapMatrixTargetSpace J₁ (D.parity i) N m t ≃ₗ[k]
      capMatrixTargetSpace D Sc cutoff i M m t.obj :=
  LinearEquiv.piCongrRight (oldContentCapSlotEquiv D Sc cutoff ν i N m t)

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Prescribed finite content entries in the chosen coordinates

Brundan--Ellis (1.13)--(1.14), DeformedMatrixComparison (4), (5):
principal and dotted fields retain the canonical source/target parity
coordinates under the genuine selected content charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open CyclotomicCrossingTensor BalancedInduction
universe u
namespace BalancedInduction
private theorem entryMate_degree_eq
    {k C A B : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {p q : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (e : p = q) (hp : IsSupernatural k p γ) (hq : IsSupernatural k q γ)
    (N : Superfunctor k A (SVec k)) (w : A) :
    orderedGridMateLinear J K hp N w = orderedGridMateLinear J K hq N w := by
  cases e
  rfl
section GenericFields
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
local instance contentEntryGenericPi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory
private theorem unit_some_total {p : ZMod 2}
    {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s} (hγ : IsSupernatural k p γ)
    {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
    (N : Superfunctor k A (SVec k)) (m : ℕ) (r : Fin m) (w : A) :
    SVec.toLinearMap ((gridUnitMatrixEntry J K hγ hβ N m (some r)).total w) =
      unitDotLinear K hβ N r.val w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • p)).iso N).hom.total w) :=
  gridUnitMatrixEntry_some_total J K hγ hβ N m r w
end GenericFields

end BalancedInduction

section GenericCoordinates
variable {k A B : Type u} [CommRing k]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (M : Superfunctor k A (SVec k)) (N : Superfunctor k B (SVec k))
  (w : A) (v : B) (e : M.obj w ≃ₗ[k] N.obj v)
local instance entryCoordinateSourcePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory
local instance entryCoordinateTargetPi : PiSupercategory k (Superfunctor k B (SVec k)) :=
  supermodulePiSupercategory

private theorem matrixPoint_source_coordinate (q : ZMod 2) :
    SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso N).hom.total v) ∘ₗ
        (shiftedModuleValueLinearEquiv M N w v e q).toLinearMap =
      e.toLinearMap ∘ₗ SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso M).hom.total w) := by
  apply LinearMap.ext
  intro b
  exact shiftedModuleValueLinearEquiv_hom_coordinate M N w v e q b

private theorem matrixPoint_target_coordinate (q : ZMod 2) :
    (shiftedModuleValueLinearEquiv M N w v e q).toLinearMap ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso M).inv.total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso N).inv.total v) ∘ₗ e.toLinearMap := by
  apply LinearMap.ext
  intro b
  exact shiftedModuleValueLinearEquiv_inv_coordinate M N w v e q b

end GenericCoordinates

private theorem matrixColumn_decorate
    {k V W X Y A B : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    (c : W →ₗ[k] Y) (f : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (z : A →ₗ[k] V) (z' : B →ₗ[k] X) (s : A →ₗ[k] B)
    (o : A →ₗ[k] W) (n : B →ₗ[k] Y)
    (h : c ∘ₗ f = g ∘ₗ d) (hz : z' ∘ₗ s = d ∘ₗ z)
    (ho : o = f ∘ₗ z) (hn : n = g ∘ₗ z') : c ∘ₗ o = n ∘ₗ s := by
  rw [ho, hn]
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun h (z b)).trans (congrArg g (LinearMap.congr_fun hz b).symm)

private theorem matrixRow_decorate
    {k V W X Y A B : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    (c : W →ₗ[k] Y) (f : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (z : W →ₗ[k] A) (z' : Y →ₗ[k] B) (s : A →ₗ[k] B)
    (o : V →ₗ[k] A) (n : X →ₗ[k] B)
    (h : c ∘ₗ f = g ∘ₗ d) (hz : s ∘ₗ z = z' ∘ₗ c)
    (ho : o = z ∘ₗ f) (hn : n = z' ∘ₗ g) : s ∘ₗ o = n ∘ₗ d := by
  rw [ho, hn]
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun hz (f b)).trans (congrArg z' (LinearMap.congr_fun h b))

private theorem square_degree_reencode
    {k V W X Y : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    (c : W →ₗ[k] Y) (f f' : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (he : f = f') (h : c ∘ₗ f = g ∘ₗ d) : c ∘ₗ f' = g ∘ₗ d := by
  rw [← he]
  exact h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i
local instance contentEntryCoordinatesPi : PiSupercategory k
    (Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) := supermodulePiSupercategory
local instance oldEntryCoordinatesPi : PiSupercategory k
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) := supermodulePiSupercategory

/-- The same literal crossing has degree p, using p²=p. -/
theorem oldContentMatrixCross_supernatural :
    IsSupernatural k (D.parity i) (oldContentEqualCross D Sc cutoff ν i) := by
  simpa only [SKM.zmod2_mul_self] using oldContentEqualCross_supernatural D Sc cutoff ν i

private theorem oldUnit_none_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i M m none).total w) =
      oldMatrixMateLinear D Sc cutoff i M w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
          (induced J ((restriction J).obj M))).hom.total w) := by
  let e := (SKM.homParityShiftDatum (k := k) (D.parity i)).iso (induced J ((restriction J).obj M))
  change SVec.toLinearMap ((e.hom ≫ matrixMateComponent D Sc cutoff i M).total w) = _
  rw [Superfunctor.comp_total, SVec.toLinearMap_comp]
  rfl

private theorem oldUnit_some_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (r : Fin m) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i M m (some r)).total w) =
      unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) M r.val w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom.total w) := by
  let e := (SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M
  change SVec.toLinearMap ((e.hom ≫ moduleUnitColumn D Sc cutoff i M r.val).total w) = _
  simp only [Superfunctor.comp_total, SVec.toLinearMap_comp, moduleUnitColumn_eq_unitDotColumn,
    unitDotColumn_total, e]

private theorem oldCap_none_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i M m none).total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
        ((restriction J).obj (induced J M))).inv.total w) ∘ₗ
          oldMatrixMateLinear D Sc cutoff i M w := by
  let e := (SKM.homParityShiftDatum (k := k) (D.parity i)).iso ((restriction J).obj (induced J M))
  change SVec.toLinearMap ((matrixMateComponent D Sc cutoff i M ≫ e.inv).total w) = _
  rw [Superfunctor.comp_total, SVec.toLinearMap_comp]
  rfl

private theorem oldCap_some_total
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (m : ℕ) (r : Fin m) (w : OldCategory D Sc cutoff) :
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i M m (some r)).total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).inv.total w) ∘ₗ
        capDotLinear J (oldAppendDot_supernatural D Sc cutoff i) M r.val w := by
  let e := (SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M
  change SVec.toLinearMap ((moduleCapRow D Sc cutoff i M r.val ≫ e.inv).total w) = _
  simp only [Superfunctor.comp_total, SVec.toLinearMap_comp, moduleCapRow_eq_capDotRow,
    capDotRow_total, e]

/-- The chosen charts intertwine the unshifted principal entry. -/
private theorem oldContentEntry_mate
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      orderedGridMateLinear J₀ J₁ (oldContentMatrixCross_supernatural D Sc cutoff ν i) N t =
    oldMatrixMateLinear D Sc cutoff i (induced Q₁ N) t.obj ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  have he := BalancedInduction.entryMate_degree_eq J₀ J₁
    (SKM.zmod2_mul_self (D.parity i))
    (oldContentEqualCross_supernatural D Sc cutoff ν i)
    (oldContentMatrixCross_supernatural D Sc cutoff ν i) N t
  exact square_degree_reencode _ _ _ _ _ he
    (oldContentMatrixCharts_mate_comp D Sc cutoff ν i N t)

/-- The first prescribed unit field retains the canonical source coordinate. -/
theorem oldContentUnitEntry_none_square
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      SVec.toLinearMap ((gridUnitMatrixEntry J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m none).total t) =
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i (induced Q₁ N) m none).total t.obj) ∘ₗ
      (oldContentUnitSlotEquiv D Sc cutoff ν i N m t none).toLinearMap := by
  have h := oldContentEntry_mate D Sc cutoff ν i N t
  have hz := matrixPoint_source_coordinate
    (induced J₀ ((restriction J₀).obj N)) (induced J ((restriction J).obj (induced Q₁ N)))
    t t.obj (oldContentEFLinearEquiv D Sc cutoff ν i N t) (D.parity i)
  have ho := gridUnitMatrixEntry_none_total J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m t
  have hn := oldUnit_none_total D Sc cutoff i (induced Q₁ N) m t.obj
  exact matrixColumn_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

/-- Every prescribed dotted unit field retains its canonical source coordinate. -/
theorem oldContentUnitEntry_some_square
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν)) (r : Fin m) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      SVec.toLinearMap ((gridUnitMatrixEntry J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m (some r)).total t) =
    SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i (induced Q₁ N) m (some r)).total t.obj) ∘ₗ
      (oldContentUnitSlotEquiv D Sc cutoff ν i N m t (some r)).toLinearMap := by
  have h : (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      unitDotLinear J₁ (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N r.val t =
    unitDotLinear J (oldAppendDot_supernatural D Sc cutoff i) (induced Q₁ N) r.val t.obj ∘ₗ
      (oldContentValueLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
    apply LinearMap.ext
    intro b
    exact oldContentFELinearEquiv_unitDot D Sc cutoff ν i N t r.val b
  have hz := matrixPoint_source_coordinate N (induced Q₁ N)
    t t.obj (oldContentValueLinearEquiv D Sc cutoff ν i N t) (r.val • D.parity i)
  have ho := BalancedInduction.unit_some_total J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m r t
  have hn := oldUnit_some_total D Sc cutoff i (induced Q₁ N) m r t.obj
  exact matrixColumn_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

/-- The principal cap field retains the canonical target coordinate. -/
theorem oldContentCapEntry_none_square
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentCapSlotEquiv D Sc cutoff ν i N m t none).toLinearMap ∘ₗ
      SVec.toLinearMap ((gridCapMatrixEntry J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff ν i) N m none).total t) =
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i (induced Q₁ N) m none).total t.obj) ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  have h := oldContentEntry_mate D Sc cutoff ν i N t
  have hz := matrixPoint_target_coordinate
    ((restriction J₁).obj (induced J₁ N)) ((restriction J).obj (induced J (induced Q₁ N)))
    t t.obj (oldContentFELinearEquiv D Sc cutoff ν i N t) (D.parity i)
  have ho := gridCapMatrixEntry_none_total J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff ν i) N m t
  have hn := oldCap_none_total D Sc cutoff i (induced Q₁ N) m t.obj
  exact matrixRow_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

/-- Every dotted cap field retains the canonical target coordinate. -/
theorem oldContentCapEntry_some_square
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν)) (r : Fin m) :
    (oldContentCapSlotEquiv D Sc cutoff ν i N m t (some r)).toLinearMap ∘ₗ
      SVec.toLinearMap ((gridCapMatrixEntry J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff ν i) N m (some r)).total t) =
    SVec.toLinearMap ((capMatrixEntry D Sc cutoff i (induced Q₁ N) m (some r)).total t.obj) ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  have h : (oldContentValueLinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      capDotLinear J₀ (oldContentAppendDot_supernatural D Sc cutoff ν i) N r.val t =
    capDotLinear J (oldAppendDot_supernatural D Sc cutoff i) (induced Q₁ N) r.val t.obj ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
    apply LinearMap.ext
    intro b
    exact oldContentEFLinearEquiv_capDot D Sc cutoff ν i N t r.val b
  have hz := matrixPoint_target_coordinate N (induced Q₁ N)
    t t.obj (oldContentValueLinearEquiv D Sc cutoff ν i N t) (r.val • D.parity i)
  have ho := gridCapMatrixEntry_some_total J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff ν i) N m r t
  have hn := oldCap_some_total D Sc cutoff i (induced Q₁ N) m r t.obj
  exact matrixRow_decorate _ _ _ _ _ _ _ _ _ h hz ho hn

end OddMath.QuiverHecke.ELV
end

end

section

/-! # The old missing-colour unit inverse in content coordinates

Brundan–Ellis (1.13) at the empty boundary: the proved-zero principal
coordinate is removed from the prescribed global inverse, and the chosen
following F/E and shifted value charts transport its remaining columns.
The input module retains the full old coefficient algebra.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
open BalancedInduction CyclotomicCrossingTensor
universe u

private def givenUnitIsoLinearEquiv {k : Type u} [CommRing k] {V W : SVec k}
    (e : V ≅ W) : V ≃ₗ[k] W where
  toLinearMap := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun f : V ⟶ V => f x) e.hom_inv_id
  right_inv x := congrArg (fun f : W ⟶ W => f x) e.inv_hom_id

private def conjugateUnitIso {k : Type u} [CommRing k] {V W V' W' : SVec k}
    (v : V ≃ₗ[k] V') (w : W ≃ₗ[k] W') (e : V' ≅ W') : V ≅ W :=
  SVec.isoOfLinearEquiv (v.trans ((givenUnitIsoLinearEquiv e).trans w.symm))

private theorem conjugateUnitIso_hom {k : Type u} [CommRing k] {V W V' W' : SVec k}
    (v : V ≃ₗ[k] V') (w : W ≃ₗ[k] W') (e : V' ≅ W') (f : V ⟶ W)
    (h : w.toLinearMap.comp f = e.hom.comp v.toLinearMap) :
    (conjugateUnitIso v w e).hom = f := by
  apply SVec.hom_ext
  intro x
  apply w.injective
  change w (w.symm (e.hom (v x))) = w (f x)
  rw [LinearEquiv.apply_symm_apply]
  exact (LinearMap.congr_fun h x).symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I) (hi : i ∉ γ)
  (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
  (w : OldContentCategory D Sc cutoff γ)
local notation "Q" => oldContentInclusion D Sc cutoff γ
local notation "G" => induced Q N
local notation "K" => oldContentAppend D Sc cutoff γ i
local notation "J" => append D Sc cutoff i
local notation "dK" => oldContentAppendDot_supernatural D Sc cutoff γ i
local notation "dJ" => oldAppendDot_supernatural D Sc cutoff i
local notation "count" => contentUnitCount D cutoff i (γ : Multiset I)

private theorem content_unitColumn_square (n : ℕ) :
    (oldContentFEChart D Sc cutoff γ i N w).toLinearMap.comp (unitDotLinear K dK N n w) =
      (unitDotLinear J dJ G n w.obj).comp (oldContentValueChart D Sc cutoff γ N w).toLinearMap := by
  apply LinearMap.ext
  intro b
  exact oldContentFEChart_unitDot D Sc cutoff γ i N w n b

private theorem globalUnitIso_hom :
    (missingColourUnitMatrixIso D Sc cutoff γ i hi N w).hom =
      unitColumnMatrix J dJ G count w.obj := by
  rw [missingColourUnitMatrixIso_hom]
  rfl

/-- The prescribed old inverse transported to native content module values,
with its actual finite shifted unit columns. No scalar-evaluation premise. -/
def contentMissingUnitMatrixIso :
    unitColumnSourceSpace (D.parity i) N count w ≅
      ((restriction K).obj ((induction K).obj N)).obj w :=
  conjugateUnitIso
    (V := unitColumnSourceSpace (D.parity i) N count w)
    (W := ((restriction K).obj ((induction K).obj N)).obj w)
    (V' := unitColumnSourceSpace (D.parity i) G count w.obj)
    (W' := ((restriction J).obj ((induction J).obj G)).obj w.obj)
    (unitColumnFamilyEquiv N G w w.obj (oldContentValueChart D Sc cutoff γ N w) (D.parity i) count)
    (oldContentFEChart D Sc cutoff γ i N w)
    (missingColourUnitMatrixIso D Sc cutoff γ i hi N w)

/-- Its forward field is the prescribed matrix of shifted ordinary unit/dot columns. -/
theorem contentMissingUnitMatrixIso_hom :
    (contentMissingUnitMatrixIso D Sc cutoff γ i hi N w).hom =
      unitColumnMatrix K dK N count w := by
  apply conjugateUnitIso_hom
  rw [globalUnitIso_hom]
  exact unitColumnMatrix_square K J dK dJ N G w w.obj
    (oldContentValueChart D Sc cutoff γ N w)
    (oldContentFEChart D Sc cutoff γ i N w).toLinearMap
    (content_unitColumn_square D Sc cutoff γ i N w) count

end OddMath.QuiverHecke.ELV
end

end
