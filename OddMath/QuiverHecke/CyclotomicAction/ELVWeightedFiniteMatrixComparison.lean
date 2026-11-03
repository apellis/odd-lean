import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixEntryComparison

/-! # Finite assembly of the prescribed weighted matrix comparisons

The finite sums and products in DeformedMatrixComparison (2), (4) retain
all given first/dotted entries. The selected coordinate products intertwine
the whole prescribed matrices before any inverse is attached.
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

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
local notation "J" => append D Sc cutoff i
local notation "Q" => oldTruncateFunctor D Sc cutoff N

private theorem oldCapMatrix_proj (P : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (m : ℕ) (w : OldCategory D Sc cutoff) (a : Option (Fin m)) :
    LinearMap.proj a ∘ₗ SVec.toLinearMap (capMatrixComponent D Sc cutoff i P m w) =
      SVec.toLinearMap ((capMatrixEntry D Sc cutoff i P m a).total w) := rfl

variable (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

private theorem newCapMatrix_proj (m : ℕ) (w : TruncatedCategory D Sc cutoff N) (a : Option (Fin m)) :
    LinearMap.proj a ∘ₗ SVec.toLinearMap (weightedCapMatrixComponent D Sc cutoff N i M m w) =
      SVec.toLinearMap ((weightedCapMatrixEntry D Sc cutoff N i M m a).total w) := rfl

/-- Every prescribed column, including the original mate slot, forms the whole finite unit square. -/
theorem weightedMatrixCharts_unitMatrix (m : ℕ) (w : OldCategory D Sc cutoff) :
    (weightedMateTargetLinearEquiv D Sc cutoff N i M w).toLinearMap ∘ₗ
        SVec.toLinearMap (unitMatrixComponent D Sc cutoff i RM m w) =
      SVec.toLinearMap (weightedUnitMatrixComponent D Sc cutoff N i M m ((Q).obj w)) ∘ₗ
        (weightedUnitMatrixValueEquiv D Sc cutoff N i M m w).toLinearMap := by
  exact columns_square _ _ _ _ _ _ _
    (fun a => weightedMatrixCharts_unitEntry D Sc cutoff N i M m a w)
    (columns_sum (fun a : Option (Fin m) => (unitMatrixFamily D Sc cutoff i RM m a).obj w) _
      (fun a => (unitMatrixEntry D Sc cutoff i RM m a).total w))
    (columns_sum (fun a : Option (Fin m) => (weightedUnitMatrixFamily D Sc cutoff N i M m a).obj ((Q).obj w)) _
      (fun a => (weightedUnitMatrixEntry D Sc cutoff N i M m a).total ((Q).obj w)))
    (fun a => piChart_proj (weightedUnitFamilyValueEquiv D Sc cutoff N i M m w) a)

/-- Every prescribed row, including the original mate slot, forms the whole finite cap square. -/
theorem weightedMatrixCharts_capMatrix (m : ℕ) (w : OldCategory D Sc cutoff) :
    (weightedCapMatrixValueEquiv D Sc cutoff N i M m w).toLinearMap ∘ₗ
        SVec.toLinearMap (capMatrixComponent D Sc cutoff i RM m w) =
      SVec.toLinearMap (weightedCapMatrixComponent D Sc cutoff N i M m ((Q).obj w)) ∘ₗ
        (weightedMateSourceLinearEquiv D Sc cutoff N i M w).toLinearMap := by
  exact rows_square _ _ _ _ _ _ _
    (fun a => weightedMatrixCharts_capEntry D Sc cutoff N i M m a w)
    (oldCapMatrix_proj D Sc cutoff i RM m w)
    (newCapMatrix_proj D Sc cutoff N i M m ((Q).obj w))
    (fun a => piChart_proj (weightedCapFamilyValueEquiv D Sc cutoff N i M m w) a)

end OddMath.QuiverHecke.ELVOld
