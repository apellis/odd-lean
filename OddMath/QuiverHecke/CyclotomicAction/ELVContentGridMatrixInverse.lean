import OddMath.QuiverHecke.CyclotomicAction.ELVContentFiniteMatrixComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixInverse
import OddMath.Algebra.HomogeneousSuperfunctorIso

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
