import OddMath.QuiverHecke.CyclotomicAction.ELVContentSuffixCrossingTransform

/-! # Outer-arrow comparison of content induction composition

Brundan--Ellis (1.9), DeformedActionAssembly §6. The existing outer-arrow
coend identity is retained as an equality of whole module maps, with the
true first intermediate content explicit. This is the suffix braid
comparison used by the selected weight charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Composition intertwines an arrow on the second inducing word,
with both endpoint casts and the true first content retained. -/
theorem contentInductionCompTo_outer_map (β : Multiset I) (σ τ τ' : List I)
    (δ γ : Multiset I) (hδ : β + (σ : Multiset I) = δ)
    (hγ : δ + (τ : Multiset I) = γ) (htγ : δ + (τ' : Multiset I) = γ)
    (h : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (ht : β + ((σ ++ τ' : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : (pres D Sc).obj (ob D τ) ⟶ (pres D Sc).obj (ob D τ')}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) :
    (contentInductionTransform D Sc cutoff N hγ htγ ha).app p
        ((contentInductionTo D Sc cutoff N β σ δ hδ).obj M) ≫
      (contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h).hom.app M =
    (contentInductionCompTo D Sc cutoff N β σ δ hδ τ' γ htγ ht).hom.app M ≫
      (contentInductionTransform D Sc cutoff N h ht
        (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha)).app p M := by
  cases hδ
  apply BalancedInduction.supernatural_ext_total
  intro z
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  change (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ hγ h).app M) z).toLinearMap ∘ₗ
      ((contentInductionTransform D Sc cutoff N hγ htγ ha).app p
        ((contentInductionTo D Sc cutoff N β σ _ rfl).obj M)).total z =
    ((contentInductionTransform D Sc cutoff N h ht
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha)).app p M).total z ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ' γ htγ ht).app M) z).toLinearMap
  rw [contentInductionTransform_total, contentInductionTransform_total]
  exact contentInductionComp_outer_arrow D Sc cutoff N β σ τ τ' γ hγ htγ h ht ha M z

end OddMath.QuiverHecke.ELVOld
