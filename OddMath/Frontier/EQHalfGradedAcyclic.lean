import OddMath.Frontier.EQDiagonal
import DG.Category.Weight
import DG.Category.Derived.Basic
import DG.HalfGraded.SuperK0

/-!
# Vanishing for arbitrary half-graded odd nilHecke modules

Ellis–Qi, Proposition 3.16(2), in the half-graded setting: for `ONH_{n+2}` the crossing
has bidegree `(-2, 1)` and differential `1`. Its copy of cohomological degree `-1` and
weight zero contracts cycles in every value of every module over the weight dg category.
In particular, parity need not equal half the internal degree in these modules.

This proves vanishing of the entire half-graded derived category in ranks at least two,
not only of objects obtained from ordinary dg modules by diagonal regrading. Both the ordinary
and super Grothendieck groups of its compact objects vanish. It makes no claim about ranks
zero and one or tensor-product multiplicativity.
-/

noncomputable section

universe w v

namespace OddMath.Frontier.EQDiagonal

open CategoryTheory Limits DG DG.HalfGradedDGRing EQOnhDG

/-- A copy of a crossing in cohomological degree `-1`, weight zero. -/
def contractionElement (n : ℕ) : (onh n).Regraded :=
  (onh n).place (-1, 0) (ONH.del 0) (by
    simpa [halfDegree] using onh_del_mem n 0)

/-- The contraction has cohomological degree `-1`. -/
theorem contractionElement_mem_grading (n : ℕ) :
    contractionElement n ∈ grading (-1) :=
  place_mem_grading (-1, 0) _

/-- Weight zero allows the same contraction to act at every weight. -/
theorem contractionElement_mem_wgrading (n : ℕ) :
    contractionElement n ∈ wgrading 0 :=
  place_mem_wgrading (-1, 0) _

/-- The original equation `d(∂₁) = 1` survives in the regraded ring. -/
theorem d_contractionElement (n : ℕ) : d (contractionElement n) = 1 := by
  rw [contractionElement, d_place, one_eq_place]
  exact place_congr (by decide) (onh_hd_del n 0) _ _

/-- The contracting endomorphism at an arbitrary weight. -/
def contractionHom (n : ℕ) (X : WeightCategory (onh n).Regraded) : X ⟶ X :=
  WeightCategory.homMk (contractionElement n) (by
    simpa using contractionElement_mem_wgrading n)

/-- The contracting endomorphism is homogeneous of degree `-1`. -/
theorem contractionHom_mem_grading (n : ℕ) (X : WeightCategory (onh n).Regraded) :
    contractionHom n X ∈ grading (-1) :=
  contractionElement_mem_grading n

/-- The identity of every weight is a boundary in the weight dg category. -/
theorem d_contractionHom (n : ℕ) (X : WeightCategory (onh n).Regraded) :
    d (contractionHom n X) = 𝟙 X :=
  WeightCategory.hom_ext (d_contractionElement n)

/-- Every half-graded module over integral `ONH_{n+2}` is acyclic at every weight.
No support restriction relating internal degree and parity is imposed on the module. -/
theorem isAcyclic_halfGraded (n : ℕ) (M : CatModule.{v} (WeightCategory (onh n).Regraded)) :
    CatModule.IsAcyclic M := by
  intro X
  refine DG.isAcyclic_iff.mpr fun k m hm hdm =>
    ⟨(contractionHom n X) • m, ?_, ?_⟩
  · have h := CatModule.smul_mem_grading (contractionHom_mem_grading n X) hm
    simpa only [neg_add_eq_sub] using h
  · rw [CatModule.d_smul (contractionHom_mem_grading n X), d_contractionHom,
      CatModule.id_smul, hdm, CatModule.smul_zero, smul_zero, add_zero]

variable {n : ℕ} [CatModule.HasDerivedCategory.{w, v} (WeightCategory (onh n).Regraded)]

/-- Every half-graded module becomes zero after localization. -/
theorem isZero_halfGraded_Q_obj (M : CatModule.{v} (WeightCategory (onh n).Regraded)) :
    IsZero (CatModule.DerivedCategory.Q.obj M) :=
  (CatModule.DerivedCategory.isZero_Q_obj_iff M).mpr (isAcyclic_halfGraded n M)

/-- The entire half-graded derived category of integral `ONH_{n+2}` vanishes. -/
theorem isZero_halfGraded_derivedCategory
    (X : CatModule.DerivedCategory.{w, v} (WeightCategory (onh n).Regraded)) : IsZero X := by
  have := Localization.essSurj (CatModule.DerivedCategory.Q (C := WeightCategory (onh n).Regraded))
    (CatModule.quasiIso (WeightCategory (onh n).Regraded))
  exact (isZero_halfGraded_Q_obj _).of_iso
    (CatModule.DerivedCategory.Q.objObjPreimageIso X).symm

/-- Every class in the ordinary Grothendieck group of compact half-graded modules vanishes. -/
theorem compactK0_eq_zero
    (x : K0 (compactSubcategory.{v}
      (CatModule.DerivedCategory.{w, v} (WeightCategory (onh n).Regraded))).FullSubcategory) :
    x = 0 := by
  induction x using K0.induction_on with
  | zero => rfl
  | mk X =>
    exact K0.mk_eq_zero_of_isZero ((IsZero.iff_id_eq_zero X).mpr (by
      ext
      exact (isZero_halfGraded_derivedCategory X.obj).eq_of_src _ _))
  | neg x hx => simp only [hx, neg_zero]
  | add x y hx hy => simp only [hx, hy, add_zero]

/-- The compact super Grothendieck group of integral half-graded `ONH_{n+2}` is zero. -/
theorem superK0c_eq_zero (x : SuperK0c.{w, v} (onh n)) : x = 0 := by
  apply (superK0cEquiv (onh n)).injective
  rw [map_zero]
  obtain ⟨y, hy⟩ := QuotientAddGroup.mk'_surjective _
    ((superK0cEquiv (onh n)) x)
  rw [← hy, compactK0_eq_zero y, map_zero]

end OddMath.Frontier.EQDiagonal
