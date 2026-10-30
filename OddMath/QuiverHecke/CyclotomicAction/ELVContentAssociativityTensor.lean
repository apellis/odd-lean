import OddMath.QuiverHecke.CyclotomicAction.ELVContentCastCoherence
/-! # Content associativity on balanced tensors

The two content composition trees of DeformedActionAssembly.md §6 agree on every nested generator.
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


theorem contentInductionComp_assoc_tensor
    (τ : List I) (γ : Multiset I) (hγ : δ₂ + (τ : Multiset I) = γ)
    (hs : δ₁ + (([j] ++ τ : List I) : Multiset I) = γ)
    (h : β + (([i,j] ++ τ : List I) : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N δ₁) (z : ContentCategory D Sc cutoff N δ₂)
    (t : ContentCategory D Sc cutoff N γ)
    (g : (contentAppendTo D Sc cutoff N δ₂ τ γ hγ).obj z ⟶ t)
    (b : (K).obj w ⟶ z) (a : (J).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionCompTo D Sc cutoff N β [i,j] δ₂ (contentPair_sum β i j)
      τ γ hγ h).hom.app M).total t
      (((BalancedInduction.induction (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)).map
      ((contentEPairComparison D Sc cutoff N β i j).hom.app M)).total t
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)
        (BalancedInduction.induced K (BalancedInduction.induced J M)).toFunctor z g
        (BalancedInduction.tensor K (BalancedInduction.induced J M).toFunctor w b
          (BalancedInduction.tensor J M.toFunctor v a m)))) =
    ((contentInductionComp D Sc cutoff N β [i]
      ([j] ++ τ) γ hs h).hom.app M).total t
      (((contentInductionComp D Sc cutoff N δ₁ [j]
        τ γ hγ hs).hom.app (BalancedInduction.induced J M)).total t
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)
        (BalancedInduction.induced K (BalancedInduction.induced J M)).toFunctor z g
        (BalancedInduction.tensor K (BalancedInduction.induced J M).toFunctor w b
          (BalancedInduction.tensor J M.toFunctor v a m)))) := by
  have hl := contentEPairComparison_comp_tensor D Sc cutoff N β i j τ γ hγ h M v w z t g b a m
  have hr := contentInductionComp_suffix_tensor D Sc cutoff N β i j τ γ hγ hs h M v w z t g b a m
  refine hl.trans ((congrArg
    (fun f => BalancedInduction.tensor (contentAppendTo D Sc cutoff N β ([i,j] ++ τ) γ h)
      M.toFunctor v f m)
    (contentInductionComp_cast_arrow D Sc cutoff N β i j τ γ hγ hs h v w z t g b a)).trans hr.symm)
end Pair
end OddMath.QuiverHecke.ELVOld
