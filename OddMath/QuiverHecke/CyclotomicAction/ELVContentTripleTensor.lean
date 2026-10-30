import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairOuterTensor
/-! # Suffix-first content induction on tensors

The second composition tree for DeformedActionAssembly.md §6, retaining its endpoint casts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
section Pair
variable (β : Multiset I) (i j : I)
local notation "δ₁" => (β + ([i] : Multiset I))
local notation "δ₂" => ((β + ([i] : Multiset I)) + ([j] : Multiset I))
local notation "J" => contentAppend D Sc cutoff N β [i]
local notation "K" => contentAppend D Sc cutoff N δ₁ [j]

theorem contentInductionComp_suffix_apply
    (τ : List I) (γ : Multiset I) (hγ : δ₂ + (τ : Multiset I) = γ)
    (hs : δ₁ + (([j] ++ τ : List I) : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N δ₁) (z : ContentCategory D Sc cutoff N δ₂)
    (t : ContentCategory D Sc cutoff N γ)
    (g : (contentAppendTo D Sc cutoff N δ₂ τ γ hγ).obj z ⟶ t)
    (b : (K).obj w ⟶ z) (n : (BalancedInduction.induced J M).obj w) :
    ((contentInductionComp D Sc cutoff N δ₁ [j] τ γ hγ hs).hom.app
      (BalancedInduction.induced J M)).total t
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)
        (BalancedInduction.induced K (BalancedInduction.induced J M)).toFunctor z g
        (BalancedInduction.tensor K (BalancedInduction.induced J M).toFunctor w b n)) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N δ₁ ([j] ++ τ) γ hs)
      (BalancedInduction.induced J M).toFunctor w
      (eqToHom (congrArg (fun F => F.obj w)
        (contentAppend_comp_eq D Sc cutoff N δ₁ [j] τ γ hγ hs)).symm ≫
        (contentAppendTo D Sc cutoff N δ₂ τ γ hγ).map b ≫ g) n := by
  unfold contentInductionComp
  apply inductionCompOfEq_hom_total_tensor

theorem contentInductionComp_suffix_tensor
    (τ : List I) (γ : Multiset I) (hγ : δ₂ + (τ : Multiset I) = γ)
    (hs : δ₁ + (([j] ++ τ : List I) : Multiset I) = γ)
    (h : β + (([i,j] ++ τ : List I) : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N δ₁) (z : ContentCategory D Sc cutoff N δ₂)
    (t : ContentCategory D Sc cutoff N γ)
    (g : (contentAppendTo D Sc cutoff N δ₂ τ γ hγ).obj z ⟶ t)
    (b : (K).obj w ⟶ z) (a : (J).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionComp D Sc cutoff N β [i]
      ([j] ++ τ) γ hs h).hom.app M).total t
      (((contentInductionComp D Sc cutoff N δ₁ [j]
        τ γ hγ hs).hom.app (BalancedInduction.induced J M)).total t
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)
        (BalancedInduction.induced K (BalancedInduction.induced J M)).toFunctor z g
        (BalancedInduction.tensor K (BalancedInduction.induced J M).toFunctor w b
          (BalancedInduction.tensor J M.toFunctor v a m)))) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N β ([i,j] ++ τ) γ h)
      M.toFunctor v
      (eqToHom (congrArg (fun F => F.obj v)
        (contentAppend_comp_eq D Sc cutoff N β [i] ([j] ++ τ) γ hs h)).symm ≫
        (contentAppendTo D Sc cutoff N δ₁ ([j] ++ τ) γ hs).map a ≫
        eqToHom (congrArg (fun F => F.obj w)
          (contentAppend_comp_eq D Sc cutoff N δ₁ [j] τ γ hγ hs)).symm ≫
        (contentAppendTo D Sc cutoff N δ₂ τ γ hγ).map b ≫ g) m := by
  have hr := contentInductionComp_suffix_apply D Sc cutoff N β i j
    τ γ hγ hs M w z t g b
      (BalancedInduction.tensor J M.toFunctor v a m)
  refine (congrArg
    (((contentInductionComp D Sc cutoff N β [i]
      ([j] ++ τ) γ hs h).hom.app M).total t) hr).trans ?_
  unfold contentInductionComp
  apply inductionCompOfEq_hom_total_tensor
end Pair
end OddMath.QuiverHecke.ELVOld
