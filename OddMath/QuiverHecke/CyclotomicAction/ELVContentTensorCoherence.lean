import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionAssociativity

/-! # Balanced tensor formulas for content comparison coherence

Pointwise formulas retain the content endpoint casts in the composition
comparisons used by DeformedActionAssembly.md §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem contentInductionCompTo_eq (β : Multiset I) (σ : List I) (δ : Multiset I)
    (hδ : β + (σ : Multiset I) = δ) (τ : List I) (γ : Multiset I)
    (hγ : δ + (τ : Multiset I) = γ)
    (h : β + ((σ ++ τ : List I) : Multiset I) = γ) :
    contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h =
      inductionCompOfEq (contentAppendTo D Sc cutoff N β σ δ hδ)
        (contentAppendTo D Sc cutoff N δ τ γ hγ)
        (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h)
        (contentAppend_compTo_eq D Sc cutoff N β σ δ hδ τ γ hγ h) := by
  subst δ
  rfl

theorem contentInductionCompTo_hom_total_tensor (β : Multiset I) (σ : List I) (δ : Multiset I)
    (hδ : β + (σ : Multiset I) = δ) (τ : List I)
    (γ : Multiset I) (h : δ + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N δ)
    (z : ContentCategory D Sc cutoff N γ)
    (g : (contentAppendTo D Sc cutoff N δ τ γ h).obj w ⟶ z)
    (a : (contentAppendTo D Sc cutoff N β σ δ hδ).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ h h').hom.app M).total z
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N δ τ γ h)
        (BalancedInduction.induced (contentAppendTo D Sc cutoff N β σ δ hδ) M).toFunctor w g
        (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ δ hδ) M.toFunctor v a m)) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h') M.toFunctor v
      (eqToHom (congrArg (fun F => F.obj v)
        (contentAppend_compTo_eq D Sc cutoff N β σ δ hδ τ γ h h')).symm ≫
        (contentAppendTo D Sc cutoff N δ τ γ h).map a ≫ g) m := by
  rw [contentInductionCompTo_eq]
  apply inductionCompOfEq_hom_total_tensor

end OddMath.QuiverHecke.ELVOld
