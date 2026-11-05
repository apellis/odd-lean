import OddMath.QuiverHecke.CyclotomicAction.ELVContentMatrixEntries

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
