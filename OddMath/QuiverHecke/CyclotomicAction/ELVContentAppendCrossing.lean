import OddMath.QuiverHecke.CyclotomicAction.ELVContentEFComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendAdjunction
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionDoubleTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendCrossing

/-! # The signed equal crossing under chosen content extension

The same-colour content matrices in DeformedMatrixComparison (2), (4)
use the prescribed signed crossing on the iterated content induction
functors. The comparison is composed from the two selected single-letter
extension maps; its coefficient action retains the complete Koszul twist.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open CategoryTheory.Functor
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
namespace BalancedInduction
private theorem even_of_app_one_zero
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (h : ∀ w, f.app 1 w = 0) :
    f ∈ parity (R := k) _ _ 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  rcases parity_eq_zero_or_one q with rfl | rfl
  · exact (hq rfl).elim
  · funext w
    exact h w

private theorem moduleMap_total_of_app_one_zero
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (h : ∀ w, f.app 1 w = 0)
    (w : A) :
    (moduleMap J f).total w = mapComponent J f 0 w := by
  have hf := even_of_app_one_zero f h
  have hi := IsSuperfunctor.map_mem (F := induction J) hf
  have hz := Superfunctor.app_eq_zero_of_mem hi (by decide : (1 : ZMod 2) ≠ 0) w
  change mapComponent J f 1 w = 0 at hz
  change mapComponent J f 0 w + mapComponent J f 1 w = mapComponent J f 0 w
  rw [hz, add_zero]

private theorem restriction_comparison_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M : Superfunctor k C (SVec k)} {N P : Superfunctor k A (SVec k)}
    (a : M ⟶ (restriction Q).obj N) (b : N ⟶ P) (v : C) (x : M.obj v) :
    (a ≫ (restriction Q).map b).total v x =
      b.total (Q.obj v) (a.total v x) := by
  rw [Superfunctor.comp_total]
  rfl
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₀" => oldContentInclusion D Sc cutoff ν
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "Q₂" => oldContentInclusion D Sc cutoff (i :: i :: ν)
local notation "J" => append D Sc cutoff i
local notation "E₀" => BalancedInduction.induction (k := k) J₀
local notation "E₁" => BalancedInduction.induction (k := k) J₁
local notation "E" => BalancedInduction.induction (k := k) J
local notation "L₀" => BalancedInduction.induction (k := k) Q₀
local notation "L₁" => BalancedInduction.induction (k := k) Q₁
local notation "R₂" => BalancedInduction.restriction (k := k) Q₂

/-- The same last equal crossing, restricted to its two-letter content block. -/
def oldContentEqualCross (s : OldContentCategory D Sc cutoff ν) :
    (J₀ ⋙ J₁).obj s ⟶ (J₀ ⋙ J₁).obj s :=
  equalCrossComponent D Sc cutoff i s.obj

theorem oldContentEqualCross_supernatural :
    IsSupernatural k (D.parity i * D.parity i) (oldContentEqualCross D Sc cutoff ν i) where
  mem s := (equalCross_supernatural D Sc cutoff i).mem s.obj
  naturality := by
    intro s t p f hf
    exact (equalCross_supernatural D Sc cutoff i).naturality hf

/-- The chosen pair comparison uses the selected following E comparison
and then the selected preceding E extension comparison. -/
def oldContentDoubleAppendRestrictionNaturalIso :
    E₀ ⋙ E₁ ≅ ((L₀ ⋙ E) ⋙ E) ⋙ R₂ :=
  isoWhiskerLeft E₀ (oldContentAppendRestrictionNaturalIso D Sc cutoff (i :: ν) i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Functor.associator _ _ _).symm R₂ ≪≫
    isoWhiskerRight (isoWhiskerRight (oldContentAppendExtensionIso D Sc cutoff ν i) E) R₂

/-- The two-letter comparison retains the selected one-letter maps in their order. -/
theorem oldContentDoubleAppendRestrictionNaturalIso_hom_app
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldContentDoubleAppendRestrictionNaturalIso D Sc cutoff ν i).hom.app M =
      (oldContentAppendRestrictionIso D Sc cutoff (i :: ν) i
        ((E₀).obj M)).hom ≫
      (R₂).map ((E).map ((oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M)) := by
  simp only [oldContentDoubleAppendRestrictionNaturalIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Functor.associator_inv_app, Category.id_comp,
    oldContentAppendRestrictionNaturalIso_hom_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Homogeneous components of the selected one-letter E extension comparison. -/
def oldContentAppendExtensionComponent (p : ZMod 2)
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj Q₁ (BalancedInduction.induced J₀ M).toFunctor w →ₗ[k]
      BalancedInduction.Obj J (BalancedInduction.induced Q₀ M).toFunctor w :=
  ((oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M).app p w

/-- The prescribed extension comparison has zero odd component. -/
theorem oldContentAppendExtensionComponent_one
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (w : OldCategory D Sc cutoff) :
    oldContentAppendExtensionComponent D Sc cutoff ν i 1 M w = 0 := by
  have hf := comp_mem (BalancedInduction.inductionComp_hom_mem J₀ Q₁ M)
    (BalancedInduction.inductionComp_inv_mem Q₀ J M)
  have hz := Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0 + 0) w
  have he := congrArg (fun f => f.app 1 w)
    (oldContentAppendExtensionIso_hom D Sc cutoff ν i M)
  exact he.trans hz

/-- Its degree-zero component is the entire selected E comparison. -/
theorem oldContentAppendExtensionComponent_zero
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (w : OldCategory D Sc cutoff) :
    oldContentAppendExtensionComponent D Sc cutoff ν i 0 M w =
      oldContentAppendExtensionLinear D Sc cutoff ν i M w := by
  change oldContentAppendExtensionComponent D Sc cutoff ν i 0 M w =
    oldContentAppendExtensionComponent D Sc cutoff ν i 0 M w +
      oldContentAppendExtensionComponent D Sc cutoff ν i 1 M w
  rw [oldContentAppendExtensionComponent_one, add_zero]

/-- Restriction of the selected E comparison on every tensor, including
its actual fully faithful inclusion unit. -/
theorem oldContentAppendRestrictionLinear_tensor
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (append D Sc cutoff i).obj s.obj ⟶ t.obj) (b : M.obj s) :
    oldContentAppendRestrictionLinear D Sc cutoff ν i M t
      (BalancedInduction.tensor J₀ M.toFunctor s g b) =
      BalancedInduction.inductionInsertedTensor Q₀ J M s t.obj g b := by
  rw [oldContentAppendRestrictionLinear_eq, LinearMap.comp_apply]
  have hu : oldContentAppendInclusionUnitLinear D Sc cutoff ν i M t
      (BalancedInduction.tensor J₀ M.toFunctor s g b) =
      BalancedInduction.tensor Q₁ (BalancedInduction.induced J₀ M).toFunctor t (𝟙 t.obj)
        (BalancedInduction.tensor J₀ M.toFunctor s g b) := rfl
  rw [hu, oldContentAppendExtensionLinear_tensor]
  exact congrArg (fun a : (J).obj s.obj ⟶ t.obj =>
    BalancedInduction.inductionInsertedTensor Q₀ J M s t.obj a b) (Category.comp_id g)

/-- The total component of the chosen two-letter comparison on literal coends. -/
def oldContentDoubleAppendRestrictionLinear
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: i :: ν)) :
    BalancedInduction.Obj J₁ (BalancedInduction.induced J₀ M).toFunctor t →ₗ[k]
      BalancedInduction.Obj J
        (BalancedInduction.induced J (BalancedInduction.induced Q₀ M)).toFunctor t.obj :=
  ((oldContentDoubleAppendRestrictionNaturalIso D Sc cutoff ν i).hom.app M).total t

/-- Its factorization retains the two independently selected single-letter maps. -/
theorem oldContentDoubleAppendRestrictionLinear_apply
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: i :: ν))
    (z : BalancedInduction.Obj J₁ (BalancedInduction.induced J₀ M).toFunctor t) :
    oldContentDoubleAppendRestrictionLinear D Sc cutoff ν i M t z =
      BalancedInduction.mapComponent J ((oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M)
        0 t.obj (oldContentAppendRestrictionLinear D Sc cutoff (i :: ν) i ((E₀).obj M) t z) := by
  have hodd (w : OldCategory D Sc cutoff) :
      ((oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M).app 1 w = 0 :=
    oldContentAppendExtensionComponent_one D Sc cutoff ν i M w
  have hm := BalancedInduction.moduleMap_total_of_app_one_zero J
    ((oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M) hodd t.obj
  have he := congrArg (fun f => f.total t z)
    (oldContentDoubleAppendRestrictionNaturalIso_hom_app D Sc cutoff ν i M)
  have hc := BalancedInduction.restriction_comparison_total Q₂
    (oldContentAppendRestrictionIso D Sc cutoff (i :: ν) i ((E₀).obj M)).hom
    ((E).map ((oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M)) t z
  have hx := LinearMap.congr_fun hm
    ((oldContentAppendRestrictionIso D Sc cutoff (i :: ν) i ((E₀).obj M)).hom.total t z)
  exact he.trans (hc.trans hx)

/-- Both selected append comparisons retain their literal nested coefficient arrows. -/
theorem oldContentDoubleAppendRestrictionLinear_tensor
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (v : OldContentCategory D Sc cutoff (i :: ν))
    (t : OldContentCategory D Sc cutoff (i :: i :: ν))
    (a : (J).obj s.obj ⟶ v.obj) (g : (J).obj v.obj ⟶ t.obj) (b : M.obj s) :
    oldContentDoubleAppendRestrictionLinear D Sc cutoff ν i M t
      (BalancedInduction.tensor J₁ (BalancedInduction.induced J₀ M).toFunctor v g
        (BalancedInduction.tensor J₀ M.toFunctor s a b)) =
      BalancedInduction.tensor J
        (BalancedInduction.induced J (BalancedInduction.induced Q₀ M)).toFunctor v.obj g
        (BalancedInduction.tensor J (BalancedInduction.induced Q₀ M).toFunctor s.obj a
          (BalancedInduction.tensor Q₀ M.toFunctor s (𝟙 s.obj) b)) := by
  rw [oldContentDoubleAppendRestrictionLinear_apply]
  have h₁ := oldContentAppendRestrictionLinear_tensor D Sc cutoff (i :: ν) i
    ((E₀).obj M) v t g (BalancedInduction.tensor J₀ M.toFunctor s a b)
  set_option backward.dsimp.instances true in
    dsimp only [BalancedInduction.induction] at h₁ ⊢
  have hStep := congrArg (BalancedInduction.mapComponent J
    ((oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M) 0 t.obj) h₁
  refine hStep.trans ?_
  unfold BalancedInduction.inductionInsertedTensor
  have hm := BalancedInduction.mapComponent_tensor J
    ((oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M) 0 t.obj v.obj g
    (BalancedInduction.tensor Q₁ (BalancedInduction.induced J₀ M).toFunctor v (𝟙 v.obj)
      (BalancedInduction.tensor J₀ M.toFunctor s a b))
  have hf := oldContentAppendExtensionComponent_zero D Sc cutoff ν i M v.obj
  have hs := oldContentAppendExtensionLinear_tensor D Sc cutoff ν i M s v v.obj (𝟙 v.obj) a b
  have hid := congrArg (fun c : (J).obj s.obj ⟶ v.obj =>
    BalancedInduction.inductionInsertedTensor Q₀ J M s v.obj c b) (Category.comp_id a)
  have he : oldContentAppendExtensionComponent D Sc cutoff ν i 0 M v.obj
      (BalancedInduction.tensor Q₁ (BalancedInduction.induced J₀ M).toFunctor v (𝟙 v.obj)
        (BalancedInduction.tensor J₀ M.toFunctor s a b)) =
      BalancedInduction.tensor J (BalancedInduction.induced Q₀ M).toFunctor s.obj a
        (BalancedInduction.tensor Q₀ M.toFunctor s (𝟙 s.obj) b) := by
    rw [hf]
    exact hs.trans hid
  exact hm.trans (congrArg₂ (fun c z => BalancedInduction.tensor J
    (BalancedInduction.induced J (BalancedInduction.induced Q₀ M)).toFunctor v.obj c z)
    (twist_zero g) he)

end OddMath.QuiverHecke.ELVOld
