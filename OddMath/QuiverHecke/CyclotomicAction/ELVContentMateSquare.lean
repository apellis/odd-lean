import OddMath.QuiverHecke.CyclotomicAction.ELVContentAppendMate
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # The chosen content mate square

DeformedMatrixComparison (2), (4), first matrix entry: equality of the
prescribed cup-crossing-cap maps on the entire balanced source, retaining
the chosen content E/F comparisons.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open CategoryTheory.Functor
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
namespace BalancedInduction
private theorem restriction_total_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (t : C)
    (z : ((restriction Q).obj M).obj t) :
    ((restriction Q).map f).total t z = f.total (Q.obj t) z := rfl
private theorem induced_hom_ext_tensor
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (M : Superfunctor k C (SVec k)) {P : Superfunctor k A (SVec k)}
    {f g : induced J M ⟶ P}
    (h : ∀ t s a b, f.total t (tensor J M.toFunctor s a b) =
      g.total t (tensor J M.toFunctor s a b)) : f = g := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro t
  apply hom_ext
  exact h t

private theorem induced_diagram_ext
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (M : Superfunctor k C (SVec k)) {P V W : Superfunctor k A (SVec k)}
    (f : induced J M ⟶ P) (g : P ⟶ W) (a : induced J M ⟶ V) (b : V ⟶ W)
    (h : ∀ t s x y, g.total t (f.total t (tensor J M.toFunctor s x y)) =
      b.total t (a.total t (tensor J M.toFunctor s x y))) : f ≫ g = a ≫ b := by
  apply induced_hom_ext_tensor J M
  intro t s x y
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  exact h t s x y

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
    (z : Obj A ((restriction A).obj M).toFunctor t) :
    mateLinear A M f t z = f.total t z := rfl

private theorem restriction_mateLinear_total
    {k C B : Type u} [CommRing k] [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
    (Q : B ⥤ C) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (M : Superfunctor k C (SVec k))
    (f : induced A ((restriction A).obj M) ⟶ (restriction A).obj (induced A M))
    (t : B) (z : Obj A ((restriction A).obj M).toFunctor (Q.obj t)) :
    ((restriction Q).map f).total t z = mateLinear A M f (Q.obj t) z := rfl

end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)

private def matrixMateRaw
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (append D Sc cutoff i)
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M).toFunctor t →ₗ[k]
    BalancedInduction.Obj (append D Sc cutoff i) M.toFunctor
      ((append D Sc cutoff i).obj t) :=
  BalancedInduction.mateLinear (append D Sc cutoff i) M
    (matrixMateComponent D Sc cutoff i M) t

private theorem matrixMateRaw_apply
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff)
    (z : BalancedInduction.Obj (append D Sc cutoff i)
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M).toFunctor t) :
    matrixMateRaw D Sc cutoff i M t z =
      (matrixMateComponent D Sc cutoff i M).total t z :=
  BalancedInduction.mateLinear_apply (append D Sc cutoff i) M
    (matrixMateComponent D Sc cutoff i M) t z

/-- Evaluation of the selected following-composite comparison retains the
selected upper induction comparison under literal restriction. -/
theorem oldContentFERestrictionNaturalIso_total
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (z : BalancedInduction.Obj J₁ N.toFunctor ((J₁).obj t)) :
    ((oldContentFERestrictionNaturalIso D Sc cutoff (i :: ν) i).hom.app N).total t z =
      oldContentAppendRestrictionLinear D Sc cutoff (i :: ν) i N ((J₁).obj t) z := by
  rw [oldContentFERestrictionNaturalIso_hom_app]
  exact BalancedInduction.restriction_total_apply J₁
    (oldContentAppendRestrictionIso D Sc cutoff (i :: ν) i N).hom t z

private def mateRestriction_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (J₀).obj s ⟶ t) (b : N.obj ((J₀).obj s)) := by
  let z := BalancedInduction.tensor J₀ ((BalancedInduction.restriction J₀).obj N).toFunctor s g b
  have h := oldContentAppendRestrictionLinear_mate_tensor D Sc cutoff ν i N s t g b
  have hr := BalancedInduction.restriction_mateLinear_total (append D Sc cutoff i) Q₁
    (BalancedInduction.induced Q₁ N)
    (matrixMateComponent D Sc cutoff i (BalancedInduction.induced Q₁ N)) t
    (oldContentEFRestrictionLinear D Sc cutoff ν i N t z)
  have hm := matrixMateRaw_apply D Sc cutoff i (BalancedInduction.induced Q₁ N) t.obj
    (oldContentEFRestrictionLinear D Sc cutoff ν i N t z)
  set_option backward.dsimp.instances true in
    dsimp only [BalancedInduction.restriction, Superfunctor.comp, z] at h hr hm
  have hh := h.trans hm.symm
  dsimp only [matrixMateRaw] at hh
  dsimp only [oldContentInclusion] at hh hr
  exact hh.trans hr.symm

/-- Equality of the prescribed mate module maps through the selected content
E/F charts, before choosing any inverse matrix. -/
theorem oldContentMate_comparison
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    BalancedInduction.orderedGridMateComponent J₀ J₁
        (oldContentEqualCross_supernatural D Sc cutoff ν i) N ≫
      (oldContentFERestrictionNaturalIso D Sc cutoff (i :: ν) i).hom.app N =
    (oldContentEFRestrictionNaturalIso D Sc cutoff ν i).hom.app N ≫
      (BalancedInduction.restriction Q₁).map
        (matrixMateComponent D Sc cutoff i (BalancedInduction.induced Q₁ N)) := by
  apply BalancedInduction.induced_diagram_ext J₀
    ((BalancedInduction.restriction J₀).obj N)
  intro t s g b
  let z := BalancedInduction.tensor J₀ ((BalancedInduction.restriction J₀).obj N).toFunctor s g b
  have hRight := mateRestriction_tensor D Sc cutoff ν i N s t g b
  have ht := oldContentFERestrictionNaturalIso_total D Sc cutoff ν i N t
    ((BalancedInduction.orderedGridMateComponent J₀ J₁
      (oldContentEqualCross_supernatural D Sc cutoff ν i) N).total t z)
  have hg := BalancedInduction.orderedGridMateLinear_apply J₀ J₁
    (oldContentEqualCross_supernatural D Sc cutoff ν i) N t z
  have hgg := congrArg (oldContentAppendRestrictionLinear D Sc cutoff (i :: ν) i N
    ((J₁).obj t)) hg
  set_option backward.dsimp.instances true in
    dsimp only [BalancedInduction.restriction, Superfunctor.comp, z] at ht hgg ⊢
  dsimp only [oldContentInclusion] at ht hgg
  have hLeft := ht.trans hgg.symm
  have hfinal := hLeft.trans hRight
  have ha : oldContentEFRestrictionLinear D Sc cutoff ν i N t z =
      ((oldContentEFRestrictionNaturalIso D Sc cutoff ν i).hom.app N).total t z := rfl
  have haa := congrArg (((BalancedInduction.restriction Q₁).map
    (matrixMateComponent D Sc cutoff i (BalancedInduction.induced Q₁ N))).total t) ha
  set_option backward.dsimp.instances true in
    dsimp only [BalancedInduction.restriction, Superfunctor.comp, z, oldContentInclusion] at haa
  have hwhole := hfinal.trans haa
  exact hwhole

end OddMath.QuiverHecke.ELVOld
