import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleRelations
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionWhiskering

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

end OddMath.QuiverHecke.ELVOld
