import OddMath.QuiverHecke.CyclotomicAction.ELVContentEFComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendAdjunction

/-! # Literal tensors of the selected content E/F charts

The same-colour and distinct-colour matrix comparisons in
DeformedMatrixComparison section 4 use the selected full-content
extension comparisons. Their tensor formulas insert the actual inclusion
unit and retain each old coefficient arrow.
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
local notation "J" => append D Sc cutoff i
local notation "Fc" => BalancedInduction.restriction (k := k) J₀
local notation "E" => BalancedInduction.induction (k := k) J
local notation "R₁" => BalancedInduction.restriction (k := k) Q₁

/-- Restriction of the selected E comparison on each literal tensor. -/
theorem oldContentAppendRestrictionLinear_tensor
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (J).obj s.obj ⟶ t.obj) (b : M.obj s) :
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

/-- The chosen preceding E/F chart keeps the selected E and F comparisons. -/
theorem oldContentEFRestrictionNaturalIso_hom_app
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentEFRestrictionNaturalIso D Sc cutoff ν i).hom.app N =
      (oldContentAppendRestrictionIso D Sc cutoff ν i ((Fc).obj N)).hom ≫
        (R₁).map ((E).map (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom) := by
  simp only [oldContentEFRestrictionNaturalIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Functor.rightUnitor_inv_app, Functor.associator_inv_app,
    Category.id_comp, BalancedInduction.fullyFaithfulUnitNaturalIso,
    NatIso.ofComponents_hom_app, oldContentEFExtensionNaturalIso_hom_app,
    CategoryTheory.Functor.map_comp, Category.assoc,
    oldContentAppendRestrictionIso, Iso.trans_hom, Functor.mapIso_hom,
    oldContentExtensionUnitIso]
  rfl

/-- The selected preceding E/F comparison at its literal source and old target. -/
def oldContentEFRestrictionLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj J₀ ((Fc).obj N).toFunctor t →ₗ[k]
      BalancedInduction.Obj J ((BalancedInduction.restriction J).obj
        (BalancedInduction.induced Q₁ N)).toFunctor t.obj :=
  ((oldContentEFRestrictionNaturalIso D Sc cutoff ν i).hom.app N).total t

/-- Its forward map keeps the chosen E and restriction-extension comparisons. -/
theorem oldContentEFRestrictionLinear_apply
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (z : BalancedInduction.Obj J₀ ((Fc).obj N).toFunctor t) :
    oldContentEFRestrictionLinear D Sc cutoff ν i N t z =
      BalancedInduction.mapComponent J (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom
        0 t.obj (oldContentAppendRestrictionLinear D Sc cutoff ν i ((Fc).obj N) t z) := by
  have hodd (w : OldCategory D Sc cutoff) :
      (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom.app 1 w = 0 :=
    oldContentRestrictionExtensionComponent_one D Sc cutoff ν i N w
  have hm := BalancedInduction.moduleMap_total_of_app_one_zero J
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom hodd t.obj
  have he := congrArg (fun f => f.total t z)
    (oldContentEFRestrictionNaturalIso_hom_app D Sc cutoff ν i N)
  have hc := BalancedInduction.restriction_comparison_total Q₁
    (oldContentAppendRestrictionIso D Sc cutoff ν i ((Fc).obj N)).hom
    ((E).map (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom) t z
  have hx := LinearMap.congr_fun hm
    ((oldContentAppendRestrictionIso D Sc cutoff ν i ((Fc).obj N)).hom.total t z)
  exact he.trans (hc.trans hx)

/-- The chosen E/F chart inserts precisely the inclusion unit in the old coefficient module. -/
theorem oldContentEFRestrictionLinear_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (J).obj s.obj ⟶ t.obj) (b : N.obj ((J₀).obj s)) :
    oldContentEFRestrictionLinear D Sc cutoff ν i N t
      (BalancedInduction.tensor J₀ ((Fc).obj N).toFunctor s g b) =
      BalancedInduction.tensor J ((BalancedInduction.restriction J).obj
        (BalancedInduction.induced Q₁ N)).toFunctor s.obj g
        (BalancedInduction.tensor Q₁ N.toFunctor ((J₀).obj s)
          (𝟙 ((J).obj s.obj)) b) := by
  rw [oldContentEFRestrictionLinear_apply]
  have h₁ := oldContentAppendRestrictionLinear_tensor D Sc cutoff ν i ((Fc).obj N) s t g b
  have hStep := congrArg (BalancedInduction.mapComponent J
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom 0 t.obj) h₁
  refine hStep.trans ?_
  unfold BalancedInduction.inductionInsertedTensor
  have hm := BalancedInduction.mapComponent_tensor J
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom 0 t.obj s.obj g
    (BalancedInduction.tensor Q₀ ((Fc).obj N).toFunctor s (𝟙 s.obj) b)
  have hf := oldContentRestrictionExtensionComponent_zero D Sc cutoff ν i N s.obj
  have hs := oldContentRestrictionExtensionLinear_tensor D Sc cutoff ν i N s.obj s (𝟙 s.obj) b
  have he : oldContentRestrictionExtensionComponent D Sc cutoff ν i 0 N s.obj
      (BalancedInduction.tensor Q₀ ((Fc).obj N).toFunctor s (𝟙 s.obj) b) =
      BalancedInduction.tensor Q₁ N.toFunctor ((J₀).obj s) (𝟙 ((J).obj s.obj)) b := by
    rw [hf]
    exact hs.trans (congrArg (fun a => BalancedInduction.tensor Q₁ N.toFunctor
      ((J₀).obj s) a b) ((J).map_id s.obj))
  have hResult := hm.trans (congrArg₂ (fun a z => BalancedInduction.tensor J
    ((BalancedInduction.restriction J).obj (BalancedInduction.induced Q₁ N)).toFunctor
      s.obj a z) (twist_zero g) he)
  exact hResult

end OddMath.QuiverHecke.ELVOld
