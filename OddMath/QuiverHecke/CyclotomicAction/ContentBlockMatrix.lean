import OddMath.QuiverHecke.CyclotomicAction.ContentHom
import OddMath.QuiverHecke.CyclotomicAction.InductionGridRouquier
import OddMath.QuiverHecke.CyclotomicAction.ContentMatrix
import OddMath.Algebra.HomogeneousSuperfunctorIso
import OddMath.QuiverHecke.CyclotomicAction.ContentBlockExtension
import OddMath.QuiverHecke.CyclotomicAction.InductionTripleBraid
import OddMath.QuiverHecke.CyclotomicAction.FullInduction
import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.SKM.FiniteModuleLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.WeightedMatrix
import OddMath.SKM.RouquierHomPostInverse
import OddMath.QuiverHecke.CyclotomicAction.WeightMixed
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier

/-!
# Content block matrix

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The prescribed old-content dotted-unit missing-colour boundary

Brundan–Ellis (1.13): the constructed old missing-colour module inverse
supplies the existing finite boundary-coefficient record at any content missing the moving colour,
with the ordinary unit, the chosen dot and full old coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I) (hi : i ∉ γ)
local notation "K" => oldContentAppend D Sc cutoff γ i
local notation "hDot" => oldContentAppendDot_supernatural D Sc cutoff γ i
local notation "count" => contentUnitCount D cutoff i (γ : Multiset I)

/-- The existing finite boundary record, constructed from the prescribed
old matrix inverse rather than supplied as an action-family hypothesis. -/
def contentMissingBoundaryCoefficients :
    SKM.RouquierBoundary.Coefficients (inductionModuleAdjunction (k := k) K)
      (inductionModuleDot K hDot) (D.parity i) count :=
  inductionVacuumCoefficients K hDot count
    (contentMissingUnitModuleIso D Sc cutoff γ i hi)
    (contentMissingUnitModuleIso_hom D Sc cutoff γ i hi)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Finite assembly of the chosen content matrix comparisons

DeformedMatrixComparison (4), (5): the prescribed crossing mate and dotted
unit/cap entries assemble under the selected content E/F family charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
section FiniteKernels
variable {k : Type u} [CommRing k] {ι : Type} [Fintype ι]
  {V W : ι → Type u} {U Z : Type u}
  [∀ a, AddCommMonoid (V a)] [∀ a, Module k (V a)]
  [∀ a, AddCommMonoid (W a)] [∀ a, Module k (W a)]
  [AddCommMonoid U] [Module k U] [AddCommMonoid Z] [Module k Z]

private theorem columns_square
    (c : U →ₗ[k] Z) (f : ∀ a, V a →ₗ[k] U) (g : ∀ a, W a →ₗ[k] Z)
    (d : ∀ a, V a →ₗ[k] W a)
    (o : ((a : ι) → V a) →ₗ[k] U) (n : ((a : ι) → W a) →ₗ[k] Z)
    (s : ((a : ι) → V a) →ₗ[k] ((a : ι) → W a))
    (h : ∀ a, c ∘ₗ f a = g a ∘ₗ d a)
    (ho : o = ∑ a, f a ∘ₗ LinearMap.proj a)
    (hn : n = ∑ a, g a ∘ₗ LinearMap.proj a)
    (hs : ∀ a, LinearMap.proj a ∘ₗ s = d a ∘ₗ LinearMap.proj a) :
    c ∘ₗ o = n ∘ₗ s := by
  classical
  rw [ho, hn]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]
  change c (∑ a, f a (x a)) = ∑ a, g a ((s x) a)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact (LinearMap.congr_fun (h a) (x a)).trans (congrArg (g a) (LinearMap.congr_fun (hs a) x).symm)

omit [Fintype ι] in
private theorem rows_square
    (c : U →ₗ[k] Z) (f : ∀ a, U →ₗ[k] V a) (g : ∀ a, Z →ₗ[k] W a)
    (d : ∀ a, V a →ₗ[k] W a)
    (o : U →ₗ[k] ((a : ι) → V a)) (n : Z →ₗ[k] ((a : ι) → W a))
    (s : ((a : ι) → V a) →ₗ[k] ((a : ι) → W a))
    (h : ∀ a, d a ∘ₗ f a = g a ∘ₗ c)
    (ho : ∀ a, LinearMap.proj a ∘ₗ o = f a)
    (hn : ∀ a, LinearMap.proj a ∘ₗ n = g a)
    (hs : ∀ a, LinearMap.proj a ∘ₗ s = d a ∘ₗ LinearMap.proj a) :
    s ∘ₗ o = n ∘ₗ c := by
  apply LinearMap.ext
  intro x
  funext a
  have h1 := LinearMap.congr_fun (hs a) (o x)
  have h2 := congrArg (d a) (LinearMap.congr_fun (ho a) x)
  have h3 := LinearMap.congr_fun (h a) x
  have h4 := LinearMap.congr_fun (hn a) (c x)
  exact h1.trans (h2.trans (h3.trans h4.symm))

omit [Fintype ι] in
private theorem piChart_proj (e : ∀ a, V a ≃ₗ[k] W a) (a : ι) :
    LinearMap.proj a ∘ₗ (LinearEquiv.piCongrRight e).toLinearMap =
      (e a).toLinearMap ∘ₗ LinearMap.proj a := by
  apply LinearMap.ext
  intro x
  rfl
end FiniteKernels

section SuperspaceColumns
variable {k : Type u} [CommRing k] {ι : Type} [Fintype ι]
private theorem columns_sum (V : ι → SVec k) (W : SVec k) (f : ∀ a, V a ⟶ W) :
    SVec.toLinearMap (OddMath.FiniteSuperspace.assembleColumns V W f) =
      ∑ a, SVec.toLinearMap (f a) ∘ₗ LinearMap.proj (R := k) (φ := fun a => V a) a := by
  classical
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply, LinearMap.comp_apply]
  rfl
end SuperspaceColumns

section GridProjection
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
private theorem gridCapMatrix_proj (N : Superfunctor k A (SVec k))
    (m : ℕ) (w : A) (a : Option (Fin m)) :
    LinearMap.proj a ∘ₗ SVec.toLinearMap (gridCapMatrixComponent J K hγ hα N m w) =
      SVec.toLinearMap ((gridCapMatrixEntry J K hγ hα N m a).total w) := rfl
end GridProjection

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
private theorem oldCapMatrix_proj
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (m : ℕ) (w : OldCategory D Sc cutoff) (a : Option (Fin m)) :
    LinearMap.proj a ∘ₗ SVec.toLinearMap (capMatrixComponent D Sc cutoff i M m w) =
      SVec.toLinearMap ((capMatrixEntry D Sc cutoff i M m a).total w) := rfl

variable (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
  (m : ℕ) (t : OldContentCategory D Sc cutoff (i :: ν))

/-- The prescribed finite unit matrix commutes with the selected whole charts. -/
theorem oldContentMatrixCharts_unitMatrix :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap ∘ₗ
      SVec.toLinearMap (gridUnitMatrixComponent J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m t) =
    SVec.toLinearMap (unitMatrixComponent D Sc cutoff i (induced Q₁ N) m t.obj) ∘ₗ
      (oldContentUnitFamilyEquiv D Sc cutoff ν i N m t).toLinearMap := by
  apply columns_square _
    (fun a => SVec.toLinearMap ((gridUnitMatrixEntry J₀ J₁
      (oldContentMatrixCross_supernatural D Sc cutoff ν i)
      (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m a).total t))
    (fun a => SVec.toLinearMap ((unitMatrixEntry D Sc cutoff i (induced Q₁ N) m a).total t.obj))
    (fun a => (oldContentUnitSlotEquiv D Sc cutoff ν i N m t a).toLinearMap) _ _ _
  · intro a
    cases a with
    | none => exact oldContentUnitEntry_none_square D Sc cutoff ν i N m t
    | some r => exact oldContentUnitEntry_some_square D Sc cutoff ν i N m t r
  · exact columns_sum
      (fun a : Option (Fin m) => (gridUnitMatrixFamily J₀ (D.parity i) N m a).obj t) _
      (fun a => (gridUnitMatrixEntry J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N m a).total t)
  · exact columns_sum
      (fun a : Option (Fin m) => (unitMatrixFamily D Sc cutoff i (induced Q₁ N) m a).obj t.obj) _
      (fun a => (unitMatrixEntry D Sc cutoff i (induced Q₁ N) m a).total t.obj)
  · exact fun a => piChart_proj (oldContentUnitSlotEquiv D Sc cutoff ν i N m t) a

/-- The prescribed finite cap matrix commutes with the selected whole charts. -/
theorem oldContentMatrixCharts_capMatrix :
    (oldContentCapFamilyEquiv D Sc cutoff ν i N m t).toLinearMap ∘ₗ
      SVec.toLinearMap (gridCapMatrixComponent J₀ J₁
        (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff ν i) N m t) =
    SVec.toLinearMap (capMatrixComponent D Sc cutoff i (induced Q₁ N) m t.obj) ∘ₗ
      (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap := by
  apply rows_square _
    (fun a => SVec.toLinearMap ((gridCapMatrixEntry J₀ J₁
      (oldContentMatrixCross_supernatural D Sc cutoff ν i)
      (oldContentAppendDot_supernatural D Sc cutoff ν i) N m a).total t))
    (fun a => SVec.toLinearMap ((capMatrixEntry D Sc cutoff i (induced Q₁ N) m a).total t.obj))
    (fun a => (oldContentCapSlotEquiv D Sc cutoff ν i N m t a).toLinearMap) _ _ _
  · intro a
    cases a with
    | none => exact oldContentCapEntry_none_square D Sc cutoff ν i N m t
    | some r => exact oldContentCapEntry_some_square D Sc cutoff ν i N m t r
  · exact gridCapMatrix_proj J₀ J₁ (oldContentMatrixCross_supernatural D Sc cutoff ν i)
      (oldContentAppendDot_supernatural D Sc cutoff ν i) N m t
  · exact oldCapMatrix_proj D Sc cutoff i (induced Q₁ N) m t.obj
  · exact fun a => piChart_proj (oldContentCapSlotEquiv D Sc cutoff ν i N m t) a

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Inverses of the prescribed content E/F matrices

Brundan--Ellis (1.13)--(1.14), DeformedMatrixComparison (4), (5).
The selected genuine finite chart squares transport the literal old matrix
inverses to the given content unit/cap matrices, without an inverse premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
private theorem iso_hom_bijective {k : Type u} [CommRing k] {V W : SVec k} (e : V ≅ W) :
    Function.Bijective e.hom := by
  constructor
  · intro x y h
    have hx := congrArg (fun f : V ⟶ V => f x) e.hom_inv_id
    have hy := congrArg (fun f : V ⟶ V => f y) e.hom_inv_id
    exact hx.symm.trans ((congrArg e.inv h).trans hy)
  · intro y
    exact ⟨e.inv y, congrArg (fun f : W ⟶ W => f y) e.inv_hom_id⟩

private theorem bijective_chart_square {k V W X Y : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    (c : W ≃ₗ[k] Y) (d : V ≃ₗ[k] X) (f : V →ₗ[k] W) (g : X →ₗ[k] Y)
    (hg : Function.Bijective g) (h : c.toLinearMap ∘ₗ f = g ∘ₗ d.toLinearMap) :
    Function.Bijective f := by
  constructor
  · intro x y hxy
    apply d.injective
    apply hg.injective
    exact (LinearMap.congr_fun h x).symm.trans
      ((congrArg c hxy).trans (LinearMap.congr_fun h y))
  · intro y
    obtain ⟨x, hx⟩ := hg.surjective (c y)
    refine ⟨d.symm x, c.injective ?_⟩
    exact (LinearMap.congr_fun h (d.symm x)).trans
      ((congrArg g (d.apply_symm_apply x)).trans hx)

namespace BalancedInduction
section GenericInverse
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
  (N : Superfunctor k A (SVec k)) (m : ℕ)

/-- The literal assembled grid unit module map is even. -/
theorem gridUnitMatrixModuleMap_mem :
    gridUnitMatrixModuleMap J K hγ hβ N m ∈ parity (R := k) _ _ 0 :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr (by
    intro q hq
    funext t
    change (if q = 0 then _ else 0) = 0
    split_ifs with h
    · exact (hq h).elim
    · rfl)
/-- The literal assembled grid cap module map is even. -/
theorem gridCapMatrixModuleMap_mem :
    gridCapMatrixModuleMap J K hγ hα N m ∈ parity (R := k) _ _ 0 :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr (by
    intro q hq
    funext t
    change (if q = 0 then _ else 0) = 0
    split_ifs with h
    · exact (hq h).elim
    · rfl)

private def gridUnitIsoOfBijective
    (h : ∀ t, Function.Bijective (gridUnitMatrixComponent J K hγ hβ N m t)) :
    OddMath.FiniteSupermodule.product (gridUnitMatrixFamily J p N m) ≅
      (restriction K).obj (induced K N) :=
  HomogeneousSuperfunctorIso.ofHom (gridUnitMatrixModuleMap J K hγ hβ N m)
    (gridUnitMatrixModuleMap_mem J K hγ hβ N m)
    (fun t => SVec.isoOfLinearEquiv
      (LinearEquiv.ofBijective (gridUnitMatrixComponent J K hγ hβ N m t) (h t)))
    (fun t => (gridUnitMatrixModuleMap_total J K hγ hβ N m t).symm)
private theorem gridUnitIsoOfBijective_hom
    (h : ∀ t, Function.Bijective (gridUnitMatrixComponent J K hγ hβ N m t)) :
    (gridUnitIsoOfBijective J K hγ hβ N m h).hom = gridUnitMatrixModuleMap J K hγ hβ N m :=
  HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

private def gridCapIsoOfBijective
    (h : ∀ t, Function.Bijective (gridCapMatrixComponent J K hγ hα N m t)) :
    induced J ((restriction J).obj N) ≅
      OddMath.FiniteSupermodule.product (gridCapMatrixFamily K p N m) :=
  HomogeneousSuperfunctorIso.ofHom (gridCapMatrixModuleMap J K hγ hα N m)
    (gridCapMatrixModuleMap_mem J K hγ hα N m)
    (fun t => SVec.isoOfLinearEquiv
      (LinearEquiv.ofBijective (gridCapMatrixComponent J K hγ hα N m t) (h t)))
    (fun t => (gridCapMatrixModuleMap_total J K hγ hα N m t).symm)
private theorem gridCapIsoOfBijective_hom
    (h : ∀ t, Function.Bijective (gridCapMatrixComponent J K hγ hα N m t)) :
    (gridCapIsoOfBijective J K hγ hα N m h).hom = gridCapMatrixModuleMap J K hγ hα N m :=
  HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _
end GenericInverse
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)

private theorem oldUnit_bijective (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hh : 0 ≤ contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    Function.Bijective (unitMatrixComponent D Sc cutoff i M
      (contentUnitCount D cutoff i ((i :: ν : List I) : Multiset I)) t.obj) := by
  rw [← contentUnitMatrixComponentIso_hom D Sc cutoff M i (i :: ν) hh t]
  exact iso_hom_bijective (contentUnitMatrixComponentIso D Sc cutoff M i (i :: ν) hh t)
private theorem oldCap_bijective (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hh : contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I) ≤ 0)
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    Function.Bijective (capMatrixComponent D Sc cutoff i M
      (contentCapCount D cutoff i ((i :: ν : List I) : Multiset I)) t.obj) := by
  rw [← contentCapMatrixComponentIso_hom D Sc cutoff M i (i :: ν) hh t]
  exact iso_hom_bijective (contentCapMatrixComponentIso D Sc cutoff M i (i :: ν) hh t)

variable (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))

/-- Bijectivity of the given content unit matrix at its prescribed height/count. -/
theorem oldContentGridUnitMatrixComponent_bijective
    (hh : 0 ≤ contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    Function.Bijective (gridUnitMatrixComponent J₀ J₁
      (oldContentMatrixCross_supernatural D Sc cutoff ν i)
      (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N
      (contentUnitCount D cutoff i ((i :: ν : List I) : Multiset I)) t) := by
  exact bijective_chart_square
    (oldContentFELinearEquiv D Sc cutoff ν i N t)
    (oldContentUnitFamilyEquiv D Sc cutoff ν i N _ t) _ _
    (oldUnit_bijective D Sc cutoff ν i (induced Q₁ N) hh t)
    (oldContentMatrixCharts_unitMatrix D Sc cutoff ν i N _ t)

/-- Bijectivity of the given content cap matrix at its prescribed height/count. -/
theorem oldContentGridCapMatrixComponent_bijective
    (hh : contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I) ≤ 0)
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    Function.Bijective (gridCapMatrixComponent J₀ J₁
      (oldContentMatrixCross_supernatural D Sc cutoff ν i)
      (oldContentAppendDot_supernatural D Sc cutoff ν i) N
      (contentCapCount D cutoff i ((i :: ν : List I) : Multiset I)) t) := by
  exact bijective_chart_square
    (oldContentCapFamilyEquiv D Sc cutoff ν i N _ t)
    (oldContentEFLinearEquiv D Sc cutoff ν i N t) _ _
    (oldCap_bijective D Sc cutoff ν i (induced Q₁ N) hh t)
    (oldContentMatrixCharts_capMatrix D Sc cutoff ν i N _ t)

/-- The given content unit matrix is an isomorphism of the actual content modules. -/
def oldContentGridUnitMatrixIso
    (hh : 0 ≤ contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I)) :
    OddMath.FiniteSupermodule.product (gridUnitMatrixFamily J₀ (D.parity i) N
      (contentUnitCount D cutoff i ((i :: ν : List I) : Multiset I))) ≅
      (restriction J₁).obj (induced J₁ N) :=
  BalancedInduction.gridUnitIsoOfBijective J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N _
    (oldContentGridUnitMatrixComponent_bijective D Sc cutoff ν i N hh)

/-- The given content cap matrix is an isomorphism of the actual content modules. -/
def oldContentGridCapMatrixIso
    (hh : contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I) ≤ 0) :
    induced J₀ ((restriction J₀).obj N) ≅
      OddMath.FiniteSupermodule.product (gridCapMatrixFamily J₁ (D.parity i) N
        (contentCapCount D cutoff i ((i :: ν : List I) : Multiset I))) :=
  BalancedInduction.gridCapIsoOfBijective J₀ J₁
    (oldContentMatrixCross_supernatural D Sc cutoff ν i)
    (oldContentAppendDot_supernatural D Sc cutoff ν i) N _
    (oldContentGridCapMatrixComponent_bijective D Sc cutoff ν i N hh)

/-- The unit inverse retains exactly the prescribed forward matrix map. -/
theorem oldContentGridUnitMatrixIso_hom
    (hh : 0 ≤ contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I)) :
    (oldContentGridUnitMatrixIso D Sc cutoff ν i N hh).hom =
      gridUnitMatrixModuleMap J₀ J₁ (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i) N
        (contentUnitCount D cutoff i ((i :: ν : List I) : Multiset I)) :=
  BalancedInduction.gridUnitIsoOfBijective_hom J₀ J₁ _ _ N _ _
/-- The cap inverse retains exactly the prescribed forward matrix map. -/
theorem oldContentGridCapMatrixIso_hom
    (hh : contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I) ≤ 0) :
    (oldContentGridCapMatrixIso D Sc cutoff ν i N hh).hom =
      gridCapMatrixModuleMap J₀ J₁ (oldContentMatrixCross_supernatural D Sc cutoff ν i)
        (oldContentAppendDot_supernatural D Sc cutoff ν i) N
        (contentCapCount D cutoff i ((i :: ν : List I) : Multiset I)) :=
  BalancedInduction.gridCapIsoOfBijective_hom J₀ J₁ _ _ N _ _

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Local Rouquier records on old content modules

Brundan–Ellis (1.7)–(1.8), (1.13)–(1.14): the literal old quotient relations
and constructed prescribed matrix inverses supply the local record on
successive old-content induction edges. No local-record, inverse,
compatibility, or complete-family hypothesis remains.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J" => oldContentAppend D Sc cutoff ν i
local notation "K" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "hCross" => oldContentMatrixCross_supernatural D Sc cutoff ν i
local notation "hDotJ" => oldContentAppendDot_supernatural D Sc cutoff ν i
local notation "hDotK" => oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i

/-- The prescribed local data at minus the intermediate content height. -/
def oldContentLoc : SKM.SuperRouquierLoc (k := k)
    (inductionModuleAdjunction (k := k) J) (inductionModuleAdjunction (k := k) K)
    (inductionModuleDot J hDotJ) (inductionModuleDot K hDotK)
    (inductionModuleCross J K hCross) (D.parity i)
    (-contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I)) := by
  refine inductionModuleLoc J K hCross hDotJ hDotK
    (contentCrossingHeight D cutoff i ((i :: ν : List I) : Multiset I)) ?_ ?_
    (fun hh N => oldContentGridUnitMatrixIso D Sc cutoff ν i N hh)
    (fun hh N => oldContentGridUnitMatrixIso_hom D Sc cutoff ν i N hh)
    (fun hh N => oldContentGridCapMatrixIso D Sc cutoff ν i N hh)
    (fun hh N => oldContentGridCapMatrixIso_hom D Sc cutoff ν i N hh)
  · intro s
    have h := oldContentEqualCross_slideLeft D Sc cutoff ν i s
    rw [koszulSign_smul (R := k)] at h
    convert! h using 1
  · intro s
    have h := oldContentEqualCross_slideRight D Sc cutoff ν i s
    rw [koszulSign_smul (R := k)] at h
    convert! h using 1

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The diagonal matrix mate through canonical content charts

Brundan–Ellis (1.13)–(1.14): the prescribed negative-crossing grid mate
commutes with the selected full-content source and target charts. The
ambient map is the already inverted weighted diagonal matrix mate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
private theorem map_id_left {C : Type u} [Category.{u} C] (F : C ⥤ C)
    (v w z : C) (a : F.obj v ⟶ w) (b : w ⟶ z) :
    a ≫ b = F.map (𝟙 v) ≫ a ≫ b := by
  rw [F.map_id, Category.id_comp]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "δ" => γ + ([i] : Multiset I)
local notation "hJ" => contentBlockCanonicalSum β [i]
local notation "hK" => contentBlockCanonicalSum γ [i]
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hJ
local notation "K" => contentAppendTo D Sc cutoff N γ [i] δ hK
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "Q₂" => contentInclusion D Sc cutoff N δ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sqJ" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hJ
local notation "sqK" => contentAppendTo_inclusion D Sc cutoff N γ [i] δ hK
local notation "hα₀" => contentBlockDistinctCross_supernatural D Sc cutoff N β i i
local notation "hχ" => truncatedEqualCross_supernatural D Sc cutoff N i

/-- The prescribed equal-colour crossing has the matrix degree p_i. -/
theorem contentBlockMatrixCross_supernatural :
    IsSupernatural k (D.parity i) (contentBlockDistinctCross D Sc cutoff N β i i) :=
  (SKM.zmod2_mul_self (D.parity i)) ▸ hα₀
local notation "hα" => contentBlockMatrixCross_supernatural D Sc cutoff N β i

private theorem negativeContentCross :
    IsSupernatural k (D.parity i * D.parity i)
      (fun s => -contentBlockDistinctCross D Sc cutoff N β i i s) where
  mem s := neg_mem ((hα₀).mem s)
  naturality hf := by
    rw [Preadditive.comp_neg, (hα₀).naturality hf, Preadditive.neg_comp, smul_neg]
private theorem negativeGlobalCross :
    IsSupernatural k (D.parity i * D.parity i)
      (fun s => -truncatedEqualCrossComponent D Sc cutoff N i s) where
  mem s := neg_mem ((hχ).mem s)
  naturality hf := by
    rw [Preadditive.comp_neg, (hχ).naturality hf, Preadditive.neg_comp, smul_neg]

/-- The whole given diagonal mate commutes with its chosen canonical content charts. -/
theorem contentBlockMatrixMate_square (M : ContentModules D Sc cutoff N γ)
    (t : ContentCategory D Sc cutoff N γ) :
    fullSquareTargetLinear K Q₂ Q₁ T sqK M ((K).obj t) ((T).obj ((Q₁).obj t))
        (congrArg (fun F => F.obj t) sqK) ∘ₗ
      orderedGridMateLinear J K hα M t =
      orderedMateLinear T hχ (induced Q₁ M) ((Q₁).obj t) ∘ₗ
        fullSquareOrdinarySourceLinear J Q₁ Q₀ T sqJ
          ((restriction J).obj M) T (induced Q₁ M)
          (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M) t := by
  have h := fullContentMate_square J J K K Q₀ Q₁ Q₁ Q₂ T T
    sqJ sqJ sqK sqK (negativeContentCross D Sc cutoff N β i)
    (negativeGlobalCross D Sc cutoff N i) M
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β i M)
    (contentBlockDistinctRestriction_unit D Sc cutoff N β i M) (by
      intro s z g
      rw [Functor.map_comp, Functor.map_neg, map_twist]
      dsimp only [contentAppendTo, contentInclusion, Functor.comp_obj, Functor.comp_map]
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact map_id_left T ((T).obj s.obj) _ _
        (-truncatedEqualCrossComponent D Sc cutoff N i s.obj)
        (twist k (D.parity i * D.parity i) ((T).map g))) t
  rw [rectangularMate_negative_eq_grid J K hα₀ M t,
    mixedMate_negative_eq_ordered T hχ (induced Q₁ M) ((Q₁).obj t)] at h
  have he := gridMateLinear_degree_eq J K hα₀ (SKM.zmod2_mul_self (D.parity i)) hα M t
  exact (congrArg (fun f => fullSquareTargetLinear K Q₂ Q₁ T sqK M ((K).obj t)
    ((T).obj ((Q₁).obj t)) (congrArg (fun F => F.obj t) sqK) ∘ₗ f) he).symm.trans h

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Dotted matrix fields through canonical content charts

Brundan–Ellis (1.13)–(1.14): compare the prescribed ordinary unit/dot
columns with the selected full-inclusion charts,
retaining arbitrary input vectors and every dot power.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
private theorem unitDot_value
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (R : Superfunctor k C (SVec k)) (n : ℕ) (t : C) (b : R.obj t) :
    (unitDotColumn J hα R n).total t b = unitDotLinear J hα R n t b :=
  LinearMap.congr_fun (unitDotColumn_total J hα R n t) b

private theorem unitDot_compare
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    {p q : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    {δ : ∀ s, T.obj s ⟶ T.obj s} (hδ : IsSupernatural k q δ)
    (R : Superfunctor k C (SVec k)) (P : Superfunctor k B (SVec k))
    (n : ℕ) (s : C) (t : B)
    (c : Obj J R.toFunctor (J.obj s) → Obj T P.toFunctor (T.obj t))
    (a : R.obj s → P.obj t)
    (h : ∀ b, c (unitDotLinear J hα R n s b) = unitDotLinear T hδ P n t (a b))
    (b : R.obj s) :
    c ((unitDotColumn J hα R n).total s b) = (unitDotColumn T hδ P n).total t (a b) := by
  have hL := congrArg c (unitDot_value J hα R n s b)
  have hR := unitDot_value T hδ P n t (a b)
  exact hL.trans ((h b).trans hR.symm)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "hK" => contentBlockCanonicalSum β [i]
local notation "K" => contentAppendTo D Sc cutoff N β [i] γ hK
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sqK" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hK

/-- The canonical content unit/dot column uses the specified affine dot. -/
theorem contentBlockMatrixDot_supernatural : IsSupernatural k (D.parity i)
    (contentAppendToComponent D Sc cutoff N hK hK (dotE D Sc [i] 0)) :=
  contentAppendTo_supernatural D Sc cutoff N hK hK (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hGlobalDot" => truncatedDot_supernatural D Sc cutoff N i

/-- Every ordinary unit/dot column commutes with the selected target chart. -/
theorem contentBlockUnitDot_square (M : ContentModules D Sc cutoff N β)
    (t : ContentCategory D Sc cutoff N β) (n : ℕ) (b : M.obj t) :
    fullSquareTargetLinear K Q₁ Q₀ T sqK M ((K).obj t) ((T).obj t.obj)
      (congrArg (fun F => F.obj t) sqK) (unitDotLinear K hDot M n t b) =
      unitDotLinear T hGlobalDot (induced Q₀ M) n t.obj (unit Q₀ M.toFunctor t b) := by
  exact fullSquareTargetLinear_unitDot K Q₁ Q₀ T sqK M hDot hGlobalDot t n b (by
    intro s g
    rw [Functor.map_comp, map_twist]
    dsimp only [contentAppendTo, contentInclusion, contentAppendToComponent,
      Functor.comp_obj, Functor.comp_map]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id])

/-- The same square uses the literal total components of the specified module columns. -/
theorem contentBlockUnitDotColumn_square (M : ContentModules D Sc cutoff N β)
    (t : ContentCategory D Sc cutoff N β) (n : ℕ) (b : M.obj t) :
    fullSquareTargetLinear K Q₁ Q₀ T sqK M ((K).obj t) ((T).obj t.obj)
      (congrArg (fun F => F.obj t) sqK) ((unitDotColumn K hDot M n).total t b) =
      (unitDotColumn T hGlobalDot (induced Q₀ M) n).total t.obj (unit Q₀ M.toFunctor t b) := by
  exact unitDot_compare K T hDot hGlobalDot M (induced Q₀ M) n t t.obj
    (fullSquareTargetLinear K Q₁ Q₀ T sqK M ((K).obj t) ((T).obj t.obj)
      (congrArg (fun F => F.obj t) sqK))
    (fun x => unit Q₀ M.toFunctor t x)
    (fun x => contentBlockUnitDot_square D Sc cutoff N β i M t n x) b

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Dotted caps through the chosen canonical content source chart

Brundan–Ellis (1.13)–(1.14): every ordinary dot/counit row is compared
through the same selected source chart and input inclusion unit.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
private theorem capDot_value
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k A (SVec k)) (n : ℕ) (w : A)
    (x : Obj J ((restriction J).obj M).toFunctor w) :
    (capDotRow J hα M n).total w x = capDotLinear J hα M n w x :=
  LinearMap.congr_fun (capDotRow_total J hα M n w) x

private theorem capDot_compare
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    {p q : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    {δ : ∀ s, T.obj s ⟶ T.obj s} (hδ : IsSupernatural k q δ)
    (M : Superfunctor k A (SVec k)) (P : Superfunctor k E (SVec k)) (n : ℕ) (w : A) (z : E)
    (a : M.obj w → P.obj z)
    (c : Obj J ((restriction J).obj M).toFunctor w → Obj T ((restriction T).obj P).toFunctor z)
    (h : ∀ x, a (capDotLinear J hα M n w x) = capDotLinear T hδ P n z (c x))
    (x : Obj J ((restriction J).obj M).toFunctor w) :
    a ((capDotRow J hα M n).total w x) = (capDotRow T hδ P n).total z (c x) := by
  have hL := congrArg a (capDot_value J hα M n w x)
  have hR := capDot_value T hδ P n z (c x)
  exact hL.trans ((h x).trans hR.symm)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "hJ" => contentBlockCanonicalSum β [i]
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hJ
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sqJ" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hJ
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hGlobalDot" => truncatedDot_supernatural D Sc cutoff N i

/-- Every ordinary dot/counit row uses the given selected source chart. -/
theorem contentBlockCapDot_square (M : ContentModules D Sc cutoff N γ)
    (t : ContentCategory D Sc cutoff N γ) (n : ℕ)
    (x : Obj J ((restriction J).obj M).toFunctor t) :
    unit Q₁ M.toFunctor t (capDotLinear J hDot M n t x) =
      capDotLinear T hGlobalDot (induced Q₁ M) n t.obj
        (fullSquareOrdinarySourceLinear J Q₁ Q₀ T sqJ ((restriction J).obj M) T (induced Q₁ M)
          (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M) t x) := by
  exact fullSquareSourceLinear_capDot_unit J Q₁ Q₀ T sqJ M hDot hGlobalDot
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β i M)
    (contentBlockDistinctRestriction_unit D Sc cutoff N β i M) t (by
      intro s g
      rw [Functor.map_comp, map_twist]
      dsimp only [contentAppendTo, contentInclusion, contentAppendToComponent,
        Functor.comp_obj, Functor.comp_map]
      simp only [eqToHom_refl, Category.id_comp]) n x

/-- The square retains the literal totals of the specified module cap rows. -/
theorem contentBlockCapDotRow_square (M : ContentModules D Sc cutoff N γ)
    (t : ContentCategory D Sc cutoff N γ) (n : ℕ)
    (x : Obj J ((restriction J).obj M).toFunctor t) :
    unit Q₁ M.toFunctor t ((capDotRow J hDot M n).total t x) =
      (capDotRow T hGlobalDot (induced Q₁ M) n).total t.obj
        (fullSquareOrdinarySourceLinear J Q₁ Q₀ T sqJ ((restriction J).obj M) T (induced Q₁ M)
          (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M) t x) := by
  exact capDot_compare J T hDot hGlobalDot M (induced Q₁ M) n t t.obj
    (fun b => unit Q₁ M.toFunctor t b)
    (fullSquareOrdinarySourceLinear J Q₁ Q₀ T sqJ ((restriction J).obj M) T (induced Q₁ M)
      (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M) t)
    (fun y => contentBlockCapDot_square D Sc cutoff N β i M t n y) x

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Whole principal matrix square on content

BE (1.13)–(1.14): the selected lower E/F and upper F/E full-inclusion
charts compare the prescribed crossing mate as a whole module morphism.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
private def rawValue {k V W : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (f : V →ₗ[k] W) (x : V) : W := f x

private theorem module_map_id_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (G : Superfunctor k C (SVec k)) (w : C) (b : G.obj w) : G.map (𝟙 w) b = b := by
  exact congrArg (fun f : G.obj w ⟶ G.obj w => f b) (G.toFunctor.map_id w)

private theorem total_comp_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M N P : Superfunctor k C (SVec k)} (f : M ⟶ N) (g : N ⟶ P) (w : C) (b : M.obj w) :
    (f ≫ g).total w b = g.total w (f.total w b) := by
  rw [Superfunctor.comp_total]
  rfl

private theorem restricted_total_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (w : C) (b : M.obj (Q.obj w)) :
    ((restriction Q).map f).total w b = f.total (Q.obj w) b := rfl

private theorem identity_total_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (w : C) (b : M.obj w) :
    (𝟙 M : M ⟶ M).total w b = b := by
  have h := SuperNatTrans.id_total (R := k) M.toFunctor w
  exact congrArg (fun f => f b) h

private theorem fullyFaithfulUnit_total_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q] [Q.Full] [Q.Faithful]
    (M : Superfunctor k C (SVec k)) (w : C) (b : M.obj w) :
    (fullyFaithfulUnitIso Q M).hom.total w b = unit Q M.toFunctor w b := by
  rw [fullyFaithfulUnitIso_hom]
  simp only [adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ite_true, one_ne_zero, ite_false, add_zero]
  rfl

private theorem restrictionLinear_total_apply
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (h : J ⋙ U = Q ⋙ T) (M : Superfunctor k C (SVec k)) (w : A)
    (b : Obj J M.toFunctor w) :
    fullSquareRestrictionLinear J U Q T h M w b =
      (fullSquareRestrictionIso J U Q T h M).hom.total w b := rfl

private theorem targetLinear_total_apply
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (h : J ⋙ U = Q ⋙ T) (M : Superfunctor k C (SVec k)) (w : A)
    (z : E) (hz : U.obj w = z) (x : Obj J M.toFunctor w) :
    rawValue (fullSquareTargetLinear J U Q T h M w z hz) x =
      postcompose T (induced Q M).toFunctor (eqToHom hz)
        ((fullSquareRestrictionIso J U Q T h M).hom.total w x) := rfl

private theorem induced_map_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (T : C ⥤ A) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (M : Superfunctor k C (SVec k)) {w z : A} (f : w ⟶ z) (x : (induced T M).obj w) :
    (induced T M).map f x = postcompose T M.toFunctor f x := rfl

private theorem sourcePostcompose_total_apply
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (h : J ⋙ U = Q ⋙ T) (R : Superfunctor k C (SVec k)) (S : Superfunctor k B (SVec k))
    (e : induced Q R ≅ S) (V : Superfunctor k E (SVec k)) (g : induced T S ⟶ V)
    (w : A) (x : (induced J R).obj w) :
    ((fullSquareSourceIso J U Q T h R S e).hom ≫ (restriction U).map g).total w x =
      g.total (U.obj w) (fullSquareSourceLinear J U Q T h R S e w x) := by
  rw [total_comp_apply, restricted_total_apply]
  rfl

private theorem sourcePostcomposeOrdinary_total_apply
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (h : J ⋙ U = Q ⋙ T) (R : Superfunctor k C (SVec k))
    (L : B ⥤ B) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (G : Superfunctor k B (SVec k)) (e : induced Q R ≅ (restriction L).obj G)
    (he : e.hom ∈ parity (R := k) _ _ 0)
    (V : Superfunctor k E (SVec k)) (g : induced T ((restriction L).obj G) ⟶ V)
    (w : A) (x : (induced J R).obj w) :
    ((fullSquareSourceIso J U Q T h R ((restriction L).obj G) e).hom ≫
      (restriction U).map g).total w x =
      g.total (U.obj w) (fullSquareOrdinarySourceLinear J U Q T h R L G e w x) := by
  have h0 := sourcePostcompose_total_apply J U Q T h R ((restriction L).obj G) e V g w x
  have h1 := congrArg (fun f => g.total (U.obj w) (f x))
    (fullSquareOrdinarySourceLinear_eq_source J U Q T h R L G e he w)
  exact h0.trans h1.symm

private theorem gridMate_congr
    {k C A B : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    {p : ZMod 2} {α β : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β) (e : α = β)
    (M : Superfunctor k A (SVec k)) :
    orderedGridMateComponent J K hα M = orderedGridMateComponent J K hβ M := by
  cases e
  rfl

private theorem module_total_congr
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} {f g : F ⟶ G} (e : f = g) (w : C) :
    f.total w = g.total w := congrArg (fun f : F ⟶ G => f.total w) e

private theorem componentSquare_apply
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (Q : A ⥤ E) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (T : E ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    {q : ZMod 2}
    {χ : ∀ s, (T ⋙ T).obj s ⟶ (T ⋙ T).obj s}
    (hχ : IsSupernatural k q χ)
    (M : Superfunctor k A (SVec k)) (R : Superfunctor k C (SVec k))
    (G : Superfunctor k E (SVec k))
    (f : induced J R ⟶ (restriction K).obj (induced K M)) (w : A)
    (c : Obj K M.toFunctor (K.obj w) →ₗ[k] Obj T G.toFunctor (T.obj (Q.obj w)))
    (d : Obj J R.toFunctor w →ₗ[k]
      Obj T ((restriction T).obj G).toFunctor (Q.obj w))
    (h : c ∘ₗ f.total w = orderedMateLinear T hχ G (Q.obj w) ∘ₗ d)
    (x : (induced J R).obj w) :
    @Eq (((restriction Q).obj ((restriction T).obj (induced T G))).obj w)
      (rawValue c (f.total w x))
      (orderedMateLinear T hχ G (Q.obj w) (d x)) :=
  LinearMap.congr_fun h x

private theorem principalSquare_of_raw
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
    (Q₀ : C ⥤ E) [Q₀.Additive] [Q₀.Linear k] [IsSuperfunctor k Q₀]
    (Q₁ : A ⥤ E) [Q₁.Additive] [Q₁.Linear k] [IsSuperfunctor k Q₁] [Q₁.Full] [Q₁.Faithful]
    (Q₂ : B ⥤ E) [Q₂.Additive] [Q₂.Linear k] [IsSuperfunctor k Q₂] [Q₂.Full] [Q₂.Faithful]
    (T : E ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (sqJ : J ⋙ Q₁ = Q₀ ⋙ T) (sqK : K ⋙ Q₂ = Q₁ ⋙ T)
    {q : ZMod 2} {χ : ∀ s, (T ⋙ T).obj s ⟶ (T ⋙ T).obj s}
    (hχ : IsSupernatural k q χ)
    (M : Superfunctor k A (SVec k)) (R : Superfunctor k C (SVec k))
    (f : induced J R ⟶ (restriction K).obj (induced K M))
    (e : induced Q₀ R ≅ (restriction T).obj (induced Q₁ M))
    (he : e.hom ∈ parity (R := k) _ _ 0)
    (a : (restriction K).obj ((restriction Q₂).obj (induced T (induced Q₁ M))) ≅
      (restriction Q₁).obj ((restriction T).obj (induced T (induced Q₁ M))))
    (ha : ∀ w b, a.hom.total w b =
      (induced T (induced Q₁ M)).map (eqToHom (congrArg (fun F => F.obj w) sqK)) b)
    (hraw : ∀ w,
      fullSquareTargetLinear K Q₂ Q₁ T sqK M (K.obj w) (T.obj (Q₁.obj w))
        (congrArg (fun F => F.obj w) sqK) ∘ₗ f.total w =
      orderedMateLinear T hχ (induced Q₁ M) (Q₁.obj w) ∘ₗ
        fullSquareOrdinarySourceLinear J Q₁ Q₀ T sqJ R T (induced Q₁ M) e w) :
    f ≫
        (fullSquareTargetRetargetIso K Q₂ Q₁ T sqK M
          ((restriction T).obj (induced T (induced Q₁ M)))
          ((restriction T).obj (induced T (induced Q₁ M))) a (Iso.refl _)).hom =
      (fullSquareSourceIso J Q₁ Q₀ T sqJ R
        ((restriction T).obj (induced Q₁ M)) e).hom ≫
        (restriction Q₁).map (orderedMateComponent T hχ (induced Q₁ M)) := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  apply SVec.hom_ext
  intro b
  rw [total_comp_apply]
  have hRight := sourcePostcompose_total_apply J Q₁ Q₀ T sqJ R
    ((restriction T).obj (induced Q₁ M)) e
    ((restriction T).obj (induced T (induced Q₁ M)))
    (orderedMateComponent T hχ (induced Q₁ M)) w b
  have hC := fullSquareTargetRetargetIso_total_apply K Q₂ Q₁ T sqK M
    ((restriction T).obj (induced T (induced Q₁ M)))
    ((restriction T).obj (induced T (induced Q₁ M))) a (Iso.refl _) w
    ((f).total w b)
  simp only [Iso.refl_hom, identity_total_apply, ha, induced_map_apply] at hC
  have hL := targetLinear_total_apply K Q₂ Q₁ T sqK M (K.obj w) (T.obj (Q₁.obj w))
    (congrArg (fun F => F.obj w) sqK) ((f).total w b)
  have hNative := hraw w
  rw [fullSquareOrdinarySourceLinear_eq_source J Q₁ Q₀ T sqJ R T (induced Q₁ M) e he w] at hNative
  have hRaw := componentSquare_apply J K Q₁ T hχ M R (induced Q₁ M) f w _ _ hNative b
  have hCL := hC.trans hL.symm
  have hJoined := hCL.trans hRaw
  have hFinal := hJoined.trans hRight.symm
  exact hFinal

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "δ" => γ + ([i] : Multiset I)
local notation "hJ" => contentBlockCanonicalSum β [i]
local notation "hK" => contentBlockCanonicalSum γ [i]
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hJ
local notation "K" => contentAppendTo D Sc cutoff N γ [i] δ hK
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "Q₂" => contentInclusion D Sc cutoff N δ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sqJ" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hJ
local notation "sqK" => contentAppendTo_inclusion D Sc cutoff N γ [i] δ hK
local notation "hGiven" => contentBlockMatrixCross_supernatural D Sc cutoff N β i
local notation "hGlobalCross" => truncatedEqualCross_supernatural D Sc cutoff N i
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hGlobalDot" => truncatedDot_supernatural D Sc cutoff N i
private theorem restrictionSquare_map_apply
    (G : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
    (w : ContentCategory D Sc cutoff N (β + ([i] : Multiset I)))
    (b : ((restriction K).obj ((restriction Q₂).obj G)).obj w) :
    (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK G).hom.total w b =
      G.map (@eqToHom _ _ ((Q₂).obj ((K).obj w)) ((T).obj w.obj)
        (congrArg (fun F => F.obj w) sqK)) b := by
  let A₀ := (restriction K).obj ((restriction Q₂).obj G)
  change (𝟙 A₀ : A₀ ⟶ A₀).total w b = _
  rw [identity_total_apply]
  have hf : @eqToHom _ _ ((Q₂).obj ((K).obj w)) ((T).obj w.obj)
      (congrArg (fun F => F.obj w) sqK) = 𝟙 ((Q₂).obj ((K).obj w)) := rfl
  rw [hf]
  exact (module_map_id_apply G _ b).symm

private def literalCross (w : ContentCategory D Sc cutoff N β) :
    (J ⋙ K).obj w ⟶ (J ⋙ K).obj w := contentBlockDistinctCross D Sc cutoff N β i i w

private theorem literalCross_eq :
    literalCross D Sc cutoff N β i = contentBlockDistinctCross D Sc cutoff N β i i := rfl

private theorem literalCross_supernatural : IsSupernatural k (D.parity i) (literalCross D Sc cutoff N β i) where
  mem w := (hGiven).mem w
  naturality hf := (hGiven).naturality hf
local notation "hCross" => literalCross_supernatural D Sc cutoff N β i

private def principalMateLiteral (R : ContentModules D Sc cutoff N (β + ([i] : Multiset I))) :
    induced J ((restriction J).obj R) ⟶ (restriction K).obj (induced K R) :=
  orderedGridMateComponent J K hCross R

private theorem principalMateLiteral_eq (R : ContentModules D Sc cutoff N (β + ([i] : Multiset I))) :
    principalMateLiteral D Sc cutoff N β i R = orderedGridMateComponent J K hGiven R :=
  gridMate_congr J K hCross hGiven (literalCross_eq D Sc cutoff N β i) R

variable (M : ContentModules D Sc cutoff N (β + ([i] : Multiset I)))
local notation "P" => induced Q₁ M
local notation "FE" => Functor.obj (restriction T) (induced T P)
local notation "Target" => fullSquareTargetRetargetIso K Q₂ Q₁ T sqK M FE FE
  (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P)) (Iso.refl FE)
local notation "Source" => fullSquareSourceIso J Q₁ Q₀ T sqJ
  (Functor.obj (restriction J) M) (Functor.obj (restriction T) P)
  (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
local notation "Value" => contentExtensionUnitIso D Sc cutoff N γ M

private theorem restrictionSquare_total_apply
    (w : ContentCategory D Sc cutoff N (β + ([i] : Multiset I)))
    (b : ((restriction K).obj ((restriction Q₂).obj (induced T P))).obj w) :
    (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P)).hom.total w b = b := by
  let A₀ := (restriction K).obj ((restriction Q₂).obj (induced T P))
  change (𝟙 A₀ : A₀ ⟶ A₀).total w b = b
  exact identity_total_apply (k := k) _ w b

/-- The chosen whole module charts intertwine the prescribed negative-crossing mate. -/
theorem contentPrincipalMate_square :
    orderedGridMateComponent J K hGiven M ≫ (Target).hom =
      (Source).hom ≫ (restriction Q₁).map (orderedMateComponent T hGlobalCross P) := by
  rw [← principalMateLiteral_eq D Sc cutoff N β i M]
  change orderedGridMateComponent J K hCross M ≫ (Target).hom = _
  apply principalSquare_of_raw J K Q₀ Q₁ Q₂ T sqJ sqK hGlobalCross M
    ((restriction J).obj M) (orderedGridMateComponent J K hCross M)
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β i M)
    (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P))
    (restrictionSquare_map_apply D Sc cutoff N β i (induced T P))
  intro w
  have h := contentBlockMatrixMate_square D Sc cutoff N β i M w
  have hOp := module_total_congr (principalMateLiteral_eq D Sc cutoff N β i M) w
  dsimp only [orderedGridMateLinear] at h ⊢
  dsimp only [principalMateLiteral] at hOp
  rw [← hOp] at h
  exact h

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Whole dotted cap-row squares on content

BE (1.13)–(1.14): the selected lower E/F and value full-inclusion
charts compare every prescribed ordinary dotted cap row as whole module
morphisms, on all vectors and arrows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
private theorem total_comp_apply_2
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M N P : Superfunctor k C (SVec k)} (f : M ⟶ N) (g : N ⟶ P) (w : C) (b : M.obj w) :
    (f ≫ g).total w b = g.total w (f.total w b) := by
  rw [Superfunctor.comp_total]
  rfl

private theorem restricted_total_apply_2
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (w : C) (b : M.obj (Q.obj w)) :
    ((restriction Q).map f).total w b = f.total (Q.obj w) b := rfl

private theorem fullyFaithfulUnit_total_apply_2
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q] [Q.Full] [Q.Faithful]
    (M : Superfunctor k C (SVec k)) (w : C) (b : M.obj w) :
    (fullyFaithfulUnitIso Q M).hom.total w b = unit Q M.toFunctor w b := by
  rw [fullyFaithfulUnitIso_hom]
  simp only [adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ite_true, one_ne_zero, ite_false, add_zero]
  rfl

private theorem sourcePostcompose_total_apply_2
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (h : J ⋙ U = Q ⋙ T) (R : Superfunctor k C (SVec k)) (S : Superfunctor k B (SVec k))
    (e : induced Q R ≅ S) (V : Superfunctor k E (SVec k)) (g : induced T S ⟶ V)
    (w : A) (x : (induced J R).obj w) :
    ((fullSquareSourceIso J U Q T h R S e).hom ≫ (restriction U).map g).total w x =
      g.total (U.obj w) (fullSquareSourceLinear J U Q T h R S e w x) := by
  rw [total_comp_apply_2, restricted_total_apply_2]
  rfl

private theorem sourcePostcomposeOrdinary_total_apply_2
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (h : J ⋙ U = Q ⋙ T) (R : Superfunctor k C (SVec k))
    (L : B ⥤ B) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
    (G : Superfunctor k B (SVec k)) (e : induced Q R ≅ (restriction L).obj G)
    (he : e.hom ∈ parity (R := k) _ _ 0)
    (V : Superfunctor k E (SVec k)) (g : induced T ((restriction L).obj G) ⟶ V)
    (w : A) (x : (induced J R).obj w) :
    ((fullSquareSourceIso J U Q T h R ((restriction L).obj G) e).hom ≫
      (restriction U).map g).total w x =
      g.total (U.obj w) (fullSquareOrdinarySourceLinear J U Q T h R L G e w x) := by
  have h0 := sourcePostcompose_total_apply_2 J U Q T h R ((restriction L).obj G) e V g w x
  have h1 := congrArg (fun f => g.total (U.obj w) (f x))
    (fullSquareOrdinarySourceLinear_eq_source J U Q T h R L G e he w)
  exact h0.trans h1.symm

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "hJ" => contentBlockCanonicalSum β [i]
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hJ
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sqJ" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hJ
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hGlobalDot" => truncatedDot_supernatural D Sc cutoff N i
variable (M : ContentModules D Sc cutoff N (β + ([i] : Multiset I)))
local notation "P" => induced Q₁ M
local notation "Source" => fullSquareSourceIso J Q₁ Q₀ T sqJ
  (Functor.obj (restriction J) M) (Functor.obj (restriction T) P)
  (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
local notation "Value" => contentExtensionUnitIso D Sc cutoff N γ M

/-- The selected lower E/F chart is even on all input module values. -/
theorem contentMatrixSourceIso_hom_mem : (Source).hom ∈ parity (R := k) _ _ 0 :=
  fullSquareSourceIso_hom_mem J Q₁ Q₀ T sqJ ((restriction J).obj M) ((restriction T).obj P)
    (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β i M)

/-- Every literal dotted cap row commutes with the same whole E/F and value charts. -/
theorem contentMatrixCapDotRow_square (n : ℕ) :
    capDotRow J hDot M n ≫ (Value).hom =
      (Source).hom ≫ (restriction Q₁).map (capDotRow T hGlobalDot P n) := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  apply SVec.hom_ext
  intro b
  have hLeft := total_comp_apply_2 (k := k) (capDotRow J hDot M n) (Value).hom w b
  have hV := fullyFaithfulUnit_total_apply_2 Q₁ M w ((capDotRow J hDot M n).total w b)
  change (Value).hom.total w ((capDotRow J hDot M n).total w b) = _ at hV
  have hLeftValue := hLeft.trans hV
  have hRightValue := sourcePostcomposeOrdinary_total_apply_2 J Q₁ Q₀ T sqJ ((restriction J).obj M)
    T P (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
    (contentBlockRestrictionExtension_even D Sc cutoff N β i M)
    P (capDotRow T hGlobalDot P n) w b
  have hRaw := contentBlockCapDotRow_square D Sc cutoff N β i M w n b
  exact hLeftValue.trans (hRaw.trans hRightValue.symm)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Whole unit-column square at every content

BE (1.14): the selected full upper append chart and content extension
unit identify the literal ordinary unit/dot module columns. No lower
predecessor or lower append is required.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
private theorem total_comp_apply_3
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M N P : Superfunctor k C (SVec k)} (f : M ⟶ N) (g : N ⟶ P) (w : C) (b : M.obj w) :
    (f ≫ g).total w b = g.total w (f.total w b) := by
  rw [Superfunctor.comp_total]
  rfl

private theorem restricted_total_apply_3
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (w : C) (b : M.obj (Q.obj w)) :
    ((restriction Q).map f).total w b = f.total (Q.obj w) b := rfl

private theorem identity_total_apply_2
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (w : C) (b : M.obj w) :
    (𝟙 M : M ⟶ M).total w b = b := by
  have h := SuperNatTrans.id_total (R := k) M.toFunctor w
  exact congrArg (fun f => f b) h

private theorem fullyFaithfulUnit_total_apply_3
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q] [Q.Full] [Q.Faithful]
    (M : Superfunctor k C (SVec k)) (w : C) (b : M.obj w) :
    (fullyFaithfulUnitIso Q M).hom.total w b = unit Q M.toFunctor w b := by
  rw [fullyFaithfulUnitIso_hom]
  simp only [adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ite_true, one_ne_zero, ite_false, add_zero]
  rfl

private theorem restrictionLinear_total_apply_2
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (h : J ⋙ U = Q ⋙ T) (M : Superfunctor k C (SVec k)) (w : A)
    (b : Obj J M.toFunctor w) :
    fullSquareRestrictionLinear J U Q T h M w b =
      (fullSquareRestrictionIso J U Q T h M).hom.total w b := rfl

private theorem targetLinear_self
    {k C A B E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (U : A ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U] [U.Full] [U.Faithful]
    (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    (T : B ⥤ E) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
    (h : J ⋙ U = Q ⋙ T) (M : Superfunctor k C (SVec k)) (w : A) :
    fullSquareTargetLinear J U Q T h M w (U.obj w) rfl =
      fullSquareRestrictionLinear J U Q T h M w := by
  rw [fullSquareTargetLinear, eqToHom_refl, postcompose_id, LinearMap.id_comp]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "hK" => contentBlockCanonicalSum β [i]
local notation "K" => contentAppendTo D Sc cutoff N β [i] γ hK
local notation "Q" => contentInclusion D Sc cutoff N β
local notation "U" => contentInclusion D Sc cutoff N γ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sq" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hK
local notation "hDot" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hGlobalDot" => truncatedDot_supernatural D Sc cutoff N i
variable (M : ContentModules D Sc cutoff N β)
local notation "P" => induced (contentInclusion D Sc cutoff N β) M
local notation "FE" => Functor.obj (restriction (truncatedAppend D Sc cutoff N [i]))
  (induced (truncatedAppend D Sc cutoff N [i]) (induced (contentInclusion D Sc cutoff N β) M))
local notation "Target" => fullSquareTargetRetargetIso K U Q T sq M FE FE
  (contentAppendToRestrictionSquare D Sc cutoff N β [i] γ hK (induced T P)) (Iso.refl FE)
local notation "Value" => contentExtensionUnitIso D Sc cutoff N β M

/-- The selected upper full-inclusion chart is even at every output content. -/
theorem contentUnitTargetIso_hom_mem : (Target).hom ∈ parity (R := k) _ _ 0 := by
  exact fullSquareTargetRetargetIso_hom_mem K U Q T sq M FE FE
    (contentAppendToRestrictionSquare D Sc cutoff N β [i] γ hK (induced T P)) (Iso.refl FE)
    (id_mem _) (id_mem _)

/-- The selected content extension unit is even, including absent-colour contents. -/
theorem contentUnitValueIso_hom_mem : (Value).hom ∈ parity (R := k) _ _ 0 := by
  rw [contentExtensionUnitIso, fullyFaithfulUnitIso_hom]
  exact adjunctionUnit_mem Q M

private theorem restrictionSquare_total_apply_2
    (w : ContentCategory D Sc cutoff N β)
    (b : ((restriction K).obj ((restriction U).obj (induced T P))).obj w) :
    (contentAppendToRestrictionSquare D Sc cutoff N β [i] γ hK (induced T P)).hom.total w b = b := by
  let A₀ := (restriction K).obj ((restriction U).obj (induced T P))
  change (𝟙 A₀ : A₀ ⟶ A₀).total w b = b
  exact identity_total_apply_2 (k := k) _ w b

/-- The literal given unit/dot columns commute with the selected whole module
charts for every content, including the absent-predecessor boundary. -/
theorem contentUnitDotColumn_square (n : ℕ) :
    unitDotColumn K hDot M n ≫ (Target).hom =
      (Value).hom ≫ (restriction Q).map (unitDotColumn T hGlobalDot P n) := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  apply SVec.hom_ext
  intro b
  have hLeft := total_comp_apply_3 (k := k) (unitDotColumn K hDot M n) (Target).hom w b
  have hRight := total_comp_apply_3 (k := k) (Value).hom
    ((restriction Q).map (unitDotColumn T hGlobalDot P n)) w b
  have hV := fullyFaithfulUnit_total_apply_3 Q M w b
  change (Value).hom.total w b = _ at hV
  have hRestricted := restricted_total_apply_3 Q (unitDotColumn T hGlobalDot P n) w
    ((Value).hom.total w b)
  have hValue := congrArg (fun z => (unitDotColumn T hGlobalDot P n).total w.obj z) hV
  have hRightValue := hRight.trans (hRestricted.trans hValue)
  have hC := fullSquareTargetRetargetIso_total_apply K U Q T sq M FE FE
    (contentAppendToRestrictionSquare D Sc cutoff N β [i] γ hK (induced T P)) (Iso.refl FE)
    w ((unitDotColumn K hDot M n).total w b)
  simp only [Iso.refl_hom, identity_total_apply_2, restrictionSquare_total_apply_2] at hC
  have hRaw := contentBlockUnitDotColumn_square D Sc cutoff N β i M w n b
  have hE := congrArg (fun f => f ((unitDotColumn K hDot M n).total w b))
    (targetLinear_self K U Q T sq M ((K).obj w))
  have hL := restrictionLinear_total_apply_2 K U Q T sq M ((K).obj w)
    ((unitDotColumn K hDot M n).total w b)
  set_option backward.dsimp.instances true in
    dsimp only [induction] at hLeft hRightValue hC hL hE hRaw ⊢
  have hER := hE.symm.trans hRaw
  have hCL := hC.trans hL.symm
  have hJoined := hCL.trans hER
  exact hLeft.trans (hJoined.trans hRightValue.symm)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Local inverse entries of the given weighted matrix on an output content

BE (1.14): restrict the constructed weighted unit matrix inverse to its
specified output content and retain the prescribed homogeneous fields.
This also supplies the absent-predecessor boundary without a lower append.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
namespace BalancedInduction
universe u
variable {k C A : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  {ι : Type}

/-- Restriction retains the literal finite module product. -/
theorem restriction_finiteProduct (V : ι → Superfunctor k A (SVec k)) :
    (restriction Q).obj (OddMath.FiniteSupermodule.product V) =
      OddMath.FiniteSupermodule.product (fun a => (restriction Q).obj (V a)) := rfl

variable [Fintype ι]

/-- Restriction retains all columns in their literal finite product coordinate. -/
theorem restriction_finiteColumns
    {V : ι → Superfunctor k A (SVec k)} {T : Superfunctor k A (SVec k)}
    (f : ∀ a, V a ⟶ T) (hf : ∀ a, f a ∈ parity (R := k) _ _ 0) :
    eqToHom (restriction_finiteProduct Q V).symm ≫
        (restriction Q).map (OddMath.FiniteSupermodule.columnsHom f hf) =
      OddMath.FiniteSupermodule.columnsHom (fun a => (restriction Q).map (f a))
        (fun a => map_mem (restriction Q) (hf a)) := by
  change (𝟙 _ ≫ (restriction Q).map (OddMath.FiniteSupermodule.columnsHom f hf)) = _
  rw [Category.id_comp]
  apply Superfunctor.hom_ext_parity
  · intro t
    rfl
  · intro t
    rfl

end BalancedInduction
open BalancedInduction OddMath.FiniteSupermodule CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
  (β : Multiset I)
local notation "Q" => contentInclusion D Sc cutoff N β
local notation "R" => restriction (contentInclusion D Sc cutoff N β)
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "m" => contentUnitCount D cutoff i β
local notation "p" => D.parity i
local instance weightedLocalGlobalPi : PiSupercategory k
    (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) := supermodulePiSupercategory

/-- The given weighted unit matrix supplies all local inverse entries on its
output content. No inverse assumption is added. -/
def weightedContentLocalInverseFrom
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) :
    SKM.SuperSumInvFrom (k := k) ((R).map (weightedMatrixMate D Sc cutoff N i M))
      (fun n => (R).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) M n))
      p (fun n => n • p) m :=
  localInverseFromColumns p (fun n => n • p)
    ((R).mapIso ((SKM.homParityShiftDatum (k := k) p).iso
      (induced T ((restriction T).obj M))))
    (fun r => (R).mapIso ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M))
    (map_mem R ((SKM.homParityShiftDatum (k := k) p).hom_mem _))
    (fun r => map_mem R ((SKM.homParityShiftDatum (k := k) (r.val • p)).hom_mem M))
    ((R).map (weightedMatrixMate D Sc cutoff N i M))
    (fun n => (R).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) M n))
    (map_mem R (weightedMatrixMate_mem D Sc cutoff N i M))
    (fun n => map_mem R (unitDotColumn_mem T (truncatedDot_supernatural D Sc cutoff N i) M n))
    (eqToIso (restriction_finiteProduct Q (weightedUnitMatrixFamily D Sc cutoff N i M m)).symm ≪≫
      weightedContentUnitMatrixIso D Sc cutoff N i M β hh) (by
        rw [Iso.trans_hom, weightedContentUnitMatrixIso_hom]
        change eqToHom (restriction_finiteProduct Q _).symm ≫
          (R).map (columnsHom _ _) = _
        rw [restriction_finiteColumns]
        unfold restoredColumns
        congr 1
        funext a
        cases a with
        | none =>
          simp only [restoredColumn, optionRestoringIso, optionForwardColumns,
            Functor.mapIso_hom, ← CategoryTheory.Functor.map_comp, weightedUnitMatrixEntry_none]
        | some r =>
          simp only [restoredColumn, optionRestoringIso, optionForwardColumns,
            Functor.mapIso_hom, ← CategoryTheory.Functor.map_comp, weightedUnitMatrixEntry_some])

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Local inverse columns of the given weighted cap matrix

BE (1.13): the constructed weighted cap matrix inverse restricts to the
specified output content with the given mate and ordinary dot/cap fields.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
namespace BalancedInduction
universe u
variable {k C A : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  {ι : Type}

/-- Restriction retains all rows in the literal finite product coordinate. -/
theorem restriction_finiteRows
    {V : ι → Superfunctor k A (SVec k)} {S : Superfunctor k A (SVec k)}
    (f : ∀ a, S ⟶ V a) (hf : ∀ a, f a ∈ parity (R := k) _ _ 0) :
    (restriction Q).map (OddMath.FiniteSupermodule.rowsHom f hf) ≫
        eqToHom (restriction_finiteProduct Q V) =
      OddMath.FiniteSupermodule.rowsHom (fun a => (restriction Q).map (f a))
        (fun a => map_mem (restriction Q) (hf a)) := by
  change ((restriction Q).map (OddMath.FiniteSupermodule.rowsHom f hf) ≫ 𝟙 _) = _
  rw [Category.comp_id]
  apply Superfunctor.hom_ext_parity
  · intro t
    rfl
  · intro t
    rfl

end BalancedInduction
open BalancedInduction OddMath.FiniteSupermodule CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
  (β : Multiset I)
local notation "Q" => contentInclusion D Sc cutoff N β
local notation "R" => restriction (contentInclusion D Sc cutoff N β)
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "m" => contentCapCount D cutoff i β
local notation "p" => D.parity i
local instance weightedCapLocalPi : PiSupercategory k
    (Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) := supermodulePiSupercategory

/-- The given weighted cap matrix supplies every local inverse column on its
output content. The prescribed forward fields are retained without an inverse premise. -/
def weightedContentLocalInverseTo
    (hh : contentCrossingHeight D cutoff i β ≤ 0) :
    SKM.SuperSumInvTo (k := k) ((R).map (weightedMatrixMate D Sc cutoff N i M))
      (fun n => (R).map (capDotRow T (truncatedDot_supernatural D Sc cutoff N i) M n))
      p (fun n => n • p) m :=
  localInverseToRows p (fun n => n • p)
    ((R).mapIso ((SKM.homParityShiftDatum (k := k) p).iso ((restriction T).obj (induced T M))))
    (fun r => (R).mapIso ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M))
    (map_mem R ((SKM.homParityShiftDatum (k := k) p).hom_mem _))
    (fun r => map_mem R ((SKM.homParityShiftDatum (k := k) (r.val • p)).hom_mem M))
    ((R).map (weightedMatrixMate D Sc cutoff N i M))
    (fun n => (R).map (capDotRow T (truncatedDot_supernatural D Sc cutoff N i) M n))
    (map_mem R (weightedMatrixMate_mem D Sc cutoff N i M))
    (fun n => map_mem R (capDotRow_mem T (truncatedDot_supernatural D Sc cutoff N i) M n))
    (weightedContentCapMatrixIso D Sc cutoff N i M β hh ≪≫
      eqToIso (restriction_finiteProduct Q (weightedCapMatrixFamily D Sc cutoff N i M m))) (by
        rw [Iso.trans_hom, weightedContentCapMatrixIso_hom]
        change (R).map (rowsHom _ _) ≫ eqToHom (restriction_finiteProduct Q _) = _
        rw [restriction_finiteRows]
        unfold restoredRows
        congr 1
        funext a
        cases a with
        | none =>
          simp only [restoredRow, optionRestoringIso, optionForwardRows,
            Functor.mapIso_inv, ← CategoryTheory.Functor.map_comp, weightedCapMatrixEntry_none]
        | some r =>
          simp only [restoredRow, optionRestoringIso, optionForwardRows,
            Functor.mapIso_inv, ← CategoryTheory.Functor.map_comp, weightedCapMatrixEntry_some])

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Prescribed content inverses with a lower predecessor

BE (1.13)–(1.14): the given global weighted inverse transports through
the selected full-content source, target and value isomorphisms. Both
orientations retain the literal negative-crossing grid mate and every
ordinary unit/dot column or cap/dot row.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i : I)
local notation "γ" => β + ([i] : Multiset I)
local notation "δ" => γ + ([i] : Multiset I)
local notation "hJ" => contentBlockCanonicalSum β [i]
local notation "hK" => contentBlockCanonicalSum γ [i]
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hJ
local notation "K" => contentAppendTo D Sc cutoff N γ [i] δ hK
local notation "Q₀" => contentInclusion D Sc cutoff N β
local notation "Q₁" => contentInclusion D Sc cutoff N γ
local notation "Q₂" => contentInclusion D Sc cutoff N δ
local notation "T" => truncatedAppend D Sc cutoff N [i]
local notation "sqJ" => contentAppendTo_inclusion D Sc cutoff N β [i] γ hJ
local notation "sqK" => contentAppendTo_inclusion D Sc cutoff N γ [i] δ hK
local notation "hCross" => contentBlockMatrixCross_supernatural D Sc cutoff N β i
local notation "hDotJ" => contentBlockMatrixDot_supernatural D Sc cutoff N β i
local notation "hDotK" => contentBlockMatrixDot_supernatural D Sc cutoff N γ i
variable (M : ContentModules D Sc cutoff N (β + ([i] : Multiset I)))
local notation "P" => induced Q₁ M
local notation "FE" => Functor.obj (restriction T) (induced T P)
local notation "Target" => fullSquareTargetRetargetIso K Q₂ Q₁ T sqK M FE FE
  (contentAppendToRestrictionSquare D Sc cutoff N γ [i] δ hK (induced T P)) (Iso.refl FE)
local notation "Source" => fullSquareSourceIso J Q₁ Q₀ T sqJ
  (Functor.obj (restriction J) M) (Functor.obj (restriction T) P)
  (contentAppendToRestrictionExtensionIso D Sc cutoff N β i γ hJ M)
local notation "Value" => contentExtensionUnitIso D Sc cutoff N γ M

/-- The prescribed unit inverse on a supported content block is constructed
from the given weighted unit matrix, with no inverse premise. -/
theorem contentSupportedLocalInverseFrom_nonempty
    (hh : 0 ≤ contentCrossingHeight D cutoff i γ) :
    Nonempty (SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent J K hCross M)
      (unitDotColumn K hDotK M) (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i γ)) := by
  let B := weightedContentLocalInverseFrom D Sc cutoff N i P γ hh
  let a := Target
  let b := Source
  let c := Value
  have H := B.mapCoordinates (𝟭 (ContentModules D Sc cutoff N γ)) a b c
    (contentUnitTargetIso_hom_mem D Sc cutoff N γ i M)
    (contentMatrixSourceIso_hom_mem D Sc cutoff N β i M)
    (contentUnitValueIso_hom_mem D Sc cutoff N γ M)
  have hf : b.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (weightedMatrixMate D Sc cutoff N i P)) ≫ a.inv =
      orderedGridMateComponent J K hCross M := by
    have hs := contentPrincipalMate_square D Sc cutoff N β i M
    rw [← weightedMatrixMate_eq_ordered D Sc cutoff N i P] at hs
    have he := congrArg (fun f => f ≫ a.inv) hs
    dsimp only [a, b, c] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  have hg (n : ℕ) : c.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (unitDotColumn T (truncatedDot_supernatural D Sc cutoff N i) P n)) ≫ a.inv =
      unitDotColumn K hDotK M n := by
    have hs := contentUnitDotColumn_square D Sc cutoff N γ i M n
    have he := congrArg (fun f => f ≫ a.inv) hs
    dsimp only [a, b, c] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  exact ⟨by simpa only [hf, hg] using H⟩

/-- The prescribed cap inverse on a supported block retains the same chosen
principal field and all ordinary dotted rows. -/
theorem contentSupportedLocalInverseTo_nonempty
    (hh : contentCrossingHeight D cutoff i γ ≤ 0) :
    Nonempty (SKM.SuperSumInvTo (k := k) (orderedGridMateComponent J K hCross M)
      (capDotRow J hDotJ M) (D.parity i) (fun n => n • D.parity i)
      (contentCapCount D cutoff i γ)) := by
  let B := weightedContentLocalInverseTo D Sc cutoff N i P γ hh
  let a := Source
  let b := Target
  let c := Value
  have H := B.mapCoordinates (𝟭 (ContentModules D Sc cutoff N γ)) a b c
    (contentMatrixSourceIso_hom_mem D Sc cutoff N β i M)
    (contentUnitTargetIso_hom_mem D Sc cutoff N γ i M)
    (contentUnitValueIso_hom_mem D Sc cutoff N γ M)
  have hf : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (weightedMatrixMate D Sc cutoff N i P)) ≫ b.inv =
      orderedGridMateComponent J K hCross M := by
    have hs := contentPrincipalMate_square D Sc cutoff N β i M
    rw [← weightedMatrixMate_eq_ordered D Sc cutoff N i P] at hs
    have he := congrArg (fun f => f ≫ b.inv) hs
    dsimp only [a, b, c] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  have hg (n : ℕ) : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N γ)).map
      ((restriction Q₁).map (capDotRow T (truncatedDot_supernatural D Sc cutoff N i) P n)) ≫ c.inv =
      capDotRow J hDotJ M n := by
    have hs := contentMatrixCapDotRow_square D Sc cutoff N β i M n
    have he := congrArg (fun f => f ≫ c.inv) hs
    dsimp only [a, b, c] at he ⊢
    simpa only [Functor.id_map, Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
  exact ⟨by simpa only [hf, hg] using H⟩

private theorem supportedSingletonDot_mem (i : I) :
    dotE D Sc [i] 0 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1

section Targets
variable (γ' δ' : Multiset I) (hγ' : β + ([i] : Multiset I) = γ')
  (hδ' : γ' + ([i] : Multiset I) = δ')
local notation "J'" => contentAppendTo D Sc cutoff N β [i] γ' hγ'
local notation "K'" => contentAppendTo D Sc cutoff N γ' [i] δ' hδ'
local notation "hCross'" => contentTargetsGridCross_supernatural D Sc cutoff N β γ' δ' i hγ' hδ'
local notation "hDotJ'" => contentAppendTo_supernatural D Sc cutoff N hγ' hγ' (supportedSingletonDot_mem D Sc i)
local notation "hDotK'" => contentAppendTo_supernatural D Sc cutoff N hδ' hδ' (supportedSingletonDot_mem D Sc i)

/-- The constructed unit inverse retains the stored successor contents used
by the weight induction functors. -/
theorem contentTargetsLocalInverseFrom_nonempty (M' : ContentModules D Sc cutoff N γ')
    (hh : 0 ≤ contentCrossingHeight D cutoff i γ') :
    Nonempty (SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent J' K' hCross' M')
      (unitDotColumn K' hDotK' M') (D.parity i) (fun n => n • D.parity i)
      (contentUnitCount D cutoff i γ')) := by
  subst δ'
  subst γ'
  exact contentSupportedLocalInverseFrom_nonempty D Sc cutoff N β i M' hh

/-- The constructed cap inverse keeps the same two stored append targets. -/
theorem contentTargetsLocalInverseTo_nonempty (M' : ContentModules D Sc cutoff N γ')
    (hh : contentCrossingHeight D cutoff i γ' ≤ 0) :
    Nonempty (SKM.SuperSumInvTo (k := k) (orderedGridMateComponent J' K' hCross' M')
      (capDotRow J' hDotJ' M') (D.parity i) (fun n => n • D.parity i)
      (contentCapCount D cutoff i γ')) := by
  subst δ'
  subst γ'
  exact contentSupportedLocalInverseTo_nonempty D Sc cutoff N β i M' hh
end Targets

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Prescribed weight inverses on supported blocks

BE (1.13)–(1.14): transport the constructed supported-content inverse
through the selected weight mate coordinates. The same equations govern
the literal unit/power columns and cap/power rows. Standing cutoff
compatibility identifies every content count with categorical height.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)
  (β : WeightBlocks D Λ x₀) (M : ELVWeightProduct D Sc cutoff N Λ x₁)
local notation "δ" => blockSucc D Λ i h₁ β
local notation "ε" => blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β)
local notation "J" => elvBlockAppend D Sc cutoff N i Λ h₁ β
local notation "K" => elvBlockAppend D Sc cutoff N i Λ h₂ (blockSucc D Λ i h₁ β)
local notation "hCross" => contentTargetsGridCross_supernatural D Sc cutoff N
  (Subtype.val β) (Subtype.val (blockSucc D Λ i h₁ β))
  (Subtype.val (blockSucc D Λ i h₂ (blockSucc D Λ i h₁ β))) i
  (elvBlockSucc_content_eq D i Λ h₁ β)
  (elvBlockSucc_content_eq D i Λ h₂ (blockSucc D Λ i h₁ β))
local notation "φ" => SKM.rouquierMate
  (elvActionAdjunction D Sc cutoff N i Λ h₁)
  (elvActionAdjunction D Sc cutoff N i Λ h₂)
  (elvActionCross D Sc cutoff N i i Λ h₁ h₂ h₁ h₂)
local notation "hSource" => elvWeightMixedSource_obj D Sc cutoff N i i Λ h₁ h₁ β M
local notation "hTarget" => elvWeightMixedTarget_obj D Sc cutoff N i i Λ h₁ h₂ h₁ h₂ β M

/-- The supported nonpositive-height block has the prescribed weight unit inverse. -/
theorem elvWeightSupportedUnitInverse_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (hh : D.h i x₁ ≤ 0) :
    Nonempty (SKM.SuperSumInvFrom (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷
          elvF D Sc cutoff N i Λ h₂).total M δ)
      (D.parity i) (fun n => n • D.parity i) (-D.h i x₁).toNat) := by
  rw [← contentUnitCount_weightBlock D cutoff i Λ x₁ hcutoff δ]
  have hc : 0 ≤ contentCrossingHeight D cutoff i δ.1 := by
    rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x₁ hcutoff δ]
    exact neg_nonneg.mpr hh
  let B := Classical.choice (contentTargetsLocalInverseFrom_nonempty D Sc cutoff N β.1 i δ.1 ε.1
    (elvBlockSucc_content_eq D i Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₂ δ) (M δ) hc)
  let a := eqToIso hTarget
  let b := eqToIso hSource
  let c := Iso.refl (M δ)
  have hc0 : c.hom = 𝟙 (M δ) := rfl
  have H := B.mapCoordinates (𝟭 (ContentModules D Sc cutoff N δ.1)) a b c
    (eqToHom_mem_parity_zero hTarget) (eqToHom_mem_parity_zero hSource) (id_mem _)
  have hf : b.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (orderedGridMateComponent J K hCross (M δ)) ≫ a.inv = (φ).app (D.parity i) M δ := by
    have hp := elvWeightRouquierGridMate_comparison D Sc cutoff N i Λ h₁ h₂ β M
    have hs : (φ).app (D.parity i) M δ ≫ a.hom =
        b.hom ≫ orderedGridMateComponent J K hCross (M δ) := by
      simpa only [a, b, eqToIso.hom] using hp
    simpa only [Functor.id_map, ← Category.assoc] using
      (Iso.comp_inv_eq a).2 hs.symm
  have hg (n : ℕ) : c.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (unitDotColumn K (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ δ) (M δ) n) ≫ a.inv =
      (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷
          elvF D Sc cutoff N i Λ h₂).total M δ := by
    have hp := elvWeightUnitPower_localCoordinates D Sc cutoff N i Λ h₁ h₂ β M n
    have hs : (elvActionUnit D Sc cutoff N i Λ h₂ ≫
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₂) n ▷
          elvF D Sc cutoff N i Λ h₂).total M δ ≫ a.hom =
        c.hom ≫ unitDotColumn K (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₂ δ) (M δ) n := by
      simpa only [a, eqToIso.hom, hc0, Category.id_comp] using hp
    simpa only [Functor.id_map, ← Category.assoc] using
      (Iso.comp_inv_eq a).2 hs.symm
  exact ⟨by simpa only [hf, hg] using H⟩

/-- The supported nonnegative-height block has the prescribed weight cap inverse. -/
theorem elvWeightSupportedCapInverse_nonempty
    (hcutoff : (cutoff i : ℤ) = D.h i Λ) (hh : 0 ≤ D.h i x₁) :
    Nonempty (SKM.SuperSumInvTo (k := k) ((φ).app (D.parity i) M δ)
      (fun n => (elvF D Sc cutoff N i Λ h₁ ◁
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
          elvActionCounit D Sc cutoff N i Λ h₁).total M δ)
      (D.parity i) (fun n => n • D.parity i) (D.h i x₁).toNat) := by
  rw [← contentCapCount_weightBlock D cutoff i Λ x₁ hcutoff δ]
  have hc : contentCrossingHeight D cutoff i δ.1 ≤ 0 := by
    rw [contentCrossingHeight_eq_neg_weight D cutoff i Λ x₁ hcutoff δ]
    exact neg_nonpos.mpr hh
  let B := Classical.choice (contentTargetsLocalInverseTo_nonempty D Sc cutoff N β.1 i δ.1 ε.1
    (elvBlockSucc_content_eq D i Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₂ δ) (M δ) hc)
  let a := eqToIso hSource
  let b := eqToIso hTarget
  let c := Iso.refl (M δ)
  have hc0 : c.inv = 𝟙 (M δ) := rfl
  have H := B.mapCoordinates (𝟭 (ContentModules D Sc cutoff N δ.1)) a b c
    (eqToHom_mem_parity_zero hSource) (eqToHom_mem_parity_zero hTarget) (id_mem _)
  have hf : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (orderedGridMateComponent J K hCross (M δ)) ≫ b.inv = (φ).app (D.parity i) M δ := by
    have hp := elvWeightRouquierGridMate_comparison D Sc cutoff N i Λ h₁ h₂ β M
    have hs : (φ).app (D.parity i) M δ ≫ b.hom =
        a.hom ≫ orderedGridMateComponent J K hCross (M δ) := by
      simpa only [a, b, eqToIso.hom] using hp
    simpa only [Functor.id_map, ← Category.assoc] using
      (Iso.comp_inv_eq b).2 hs.symm
  have hg (n : ℕ) : a.hom ≫ (𝟭 (ContentModules D Sc cutoff N δ.1)).map
      (capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n) ≫ c.inv =
      (elvF D Sc cutoff N i Λ h₁ ◁
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
          elvActionCounit D Sc cutoff N i Λ h₁).total M δ := by
    have hs : (elvF D Sc cutoff N i Λ h₁ ◁
        SKM.rouquierPower (elvActionDot D Sc cutoff N i Λ h₁) n ≫
          elvActionCounit D Sc cutoff N i Λ h₁).total M δ =
        a.hom ≫ capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n := by
      simpa only [a, eqToIso.hom] using
        elvWeightCapPower_localCoordinates D Sc cutoff N i Λ h₁ β M n
    rw [Functor.id_map]
    calc
      a.hom ≫ capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n ≫ c.inv =
          (a.hom ≫ capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n) ≫ c.inv :=
        (Category.assoc _ _ _).symm
      _ = a.hom ≫ capDotRow J (elvBlockGridDot_supernatural D Sc cutoff N i Λ h₁ β) (M δ) n := by
        rw [hc0]
        exact Category.comp_id _
      _ = _ := hs.symm
  exact ⟨by simpa only [hf, hg] using H⟩

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The absent-predecessor boundary for the weight matrices

Brundan–Ellis (1.13)–(1.14): at an output missing i, the lower E/F
coordinate vanishes, whereas the following F/E coordinate is retained.
The standing cutoff/highest-weight match puts this boundary at
nonpositive categorical height. Strictly positive height always has
a predecessor, so its row matrix has the supported content coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- Induction after append restriction has no vector at a word lacking the appended colour. -/
theorem truncatedIndRes_subsingleton_of_not_mem (i : I)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff bound) (SVec k))
    (w : TruncatedCategory D Sc cutoff bound) (hi : i ∉ (w.word : Multiset I)) :
    Subsingleton ((induced (truncatedAppend D Sc cutoff bound [i])
      ((restriction (truncatedAppend D Sc cutoff bound [i])).obj M)).obj w) := by
  have hz : ∀ z : Obj (truncatedAppend D Sc cutoff bound [i])
      ((restriction (truncatedAppend D Sc cutoff bound [i])).obj M).toFunctor w, z = 0 := by
    apply obj_eq_zero_of_coeff_eq_zero
    intro s g
    apply truncatedCategory_hom_eq_zero_of_content_ne D Sc cutoff bound (f := g)
    intro he
    apply hi
    rw [← he]
    change i ∈ ((s.word ++ [i] : List I) : Multiset I)
    simp only [Multiset.mem_coe, List.mem_append, List.mem_singleton, or_true]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- The entire restricted E/F module is zero on a content block missing i. -/
theorem truncatedIndRes_restriction_isZero (i : I) (γ : Multiset I) (hi : i ∉ γ)
    (M : Superfunctor k (TruncatedCategory D Sc cutoff bound) (SVec k)) :
    Limits.IsZero ((restriction (contentInclusion D Sc cutoff bound γ)).obj
      (induced (truncatedAppend D Sc cutoff bound [i])
        ((restriction (truncatedAppend D Sc cutoff bound [i])).obj M))) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply Superfunctor.hom_ext
  intro p w
  apply SVec.hom_ext
  intro x
  have hs := truncatedIndRes_subsingleton_of_not_mem D Sc cutoff bound i M w.obj
    (by simpa only [w.content] using hi)
  exact hs.elim _ _

/-- An absent predecessor puts the categorical weight at nonpositive height. -/
theorem elvWeightHeight_nonpos_of_absent (i : I) (Λ : X) {x₀ x : X}
    (h : x₀ + D.α i = x) (hcutoff : (cutoff i : ℤ) = D.h i Λ)
    (δ : WeightBlocks D Λ x) (hδ : ¬ ∃ β, blockSucc D Λ i h β = δ) :
    D.h i x ≤ 0 := by
  have hi : i ∉ δ.1 := fun hm => hδ ((exists_blockSucc_iff D Λ i h δ).mpr hm)
  have hc := contentCrossingHeight_nonneg_of_not_mem D cutoff δ.1.toList i
    (by simpa only [Multiset.mem_toList] using hi)
  rw [Multiset.coe_toList, contentCrossingHeight_eq_neg_weight D cutoff i Λ x hcutoff δ] at hc
  exact neg_nonneg.mp hc

/-- Strictly positive categorical height excludes every absent predecessor sector. -/
theorem elvWeightPredecessor_of_positive_height (i : I) (Λ : X) {x₀ x : X}
    (h : x₀ + D.α i = x) (hcutoff : (cutoff i : ℤ) = D.h i Λ)
    (hpos : 0 < D.h i x) (δ : WeightBlocks D Λ x) :
    ∃ β, blockSucc D Λ i h β = δ := by
  by_contra hδ
  exact (not_lt_of_ge (elvWeightHeight_nonpos_of_absent D cutoff i Λ h hcutoff δ hδ)) hpos

end OddMath.QuiverHecke.ELVOld
end

end
