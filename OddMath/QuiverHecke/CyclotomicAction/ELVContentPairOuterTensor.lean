import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairTensor
/-! # Outer whiskering of the raising-pair tensor comparison

Pointwise formulas for the composition trees of DeformedActionAssembly.md §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem induction_map_even_tensor
    {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [(J).Additive] [(J).Linear k] [IsSuperfunctor k J]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) M N 0)
    (v : C) (w : B) (g : (J).obj v ⟶ w) (m : M.obj v) :
    ((BalancedInduction.induction J).map f).total w
      (BalancedInduction.tensor J M.toFunctor v g m) =
    BalancedInduction.tensor J N.toFunctor v g (f.total v m) := by
  have h1 := Superfunctor.app_eq_zero_of_mem hf (show (1 : ZMod 2) ≠ 0 by decide)
  change (BalancedInduction.moduleMap J f).total w _ = _
  rw [BalancedInduction.moduleMap_total_tensor, h1]
  simp only [SuperNatTrans.total, h1, add_zero]
  change BalancedInduction.tensor J N.toFunctor v g (f.app 0 v m) +
    BalancedInduction.tensor J N.toFunctor v (twist k 1 g) 0 = _
  rw [BalancedInduction.tensor_zero_right, add_zero]

section Pair
variable (β : Multiset I) (i j : I)
local notation "δ₁" => (β + ([i] : Multiset I))
local notation "δ₂" => ((β + ([i] : Multiset I)) + ([j] : Multiset I))
local notation "J" => contentAppend D Sc cutoff N β [i]
local notation "K" => contentAppendTo D Sc cutoff N δ₁ [j] δ₂ rfl
local notation "A" => contentAppendTo D Sc cutoff N β [i,j] δ₂ (contentPair_sum β i j)
local notation "e" => contentAppend_comp_eq D Sc cutoff N β [i] [j] δ₂ rfl (contentPair_sum β i j)

theorem contentEPairComparison_outer_apply
    (τ : List I) (γ : Multiset I) (hγ : δ₂ + (τ : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N δ₂) (t : ContentCategory D Sc cutoff N γ)
    (g : (contentAppendTo D Sc cutoff N δ₂ τ γ hγ).obj z ⟶ t)
    (n : (BalancedInduction.induced K (BalancedInduction.induced J M)).obj z) :
    ((BalancedInduction.induction (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)).map
      ((contentEPairComparison D Sc cutoff N β i j).hom.app M)).total t
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)
        (BalancedInduction.induced K (BalancedInduction.induced J M)).toFunctor z g n) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)
      (BalancedInduction.induced A M).toFunctor z g
      (((contentEPairComparison D Sc cutoff N β i j).hom.app M).total z n) := by
  have he : EvenComparisonAt (k := k) (contentEPairComparison D Sc cutoff N β i j) M := by
    unfold contentEPairComparison
    apply contentInductionComp_mem
  apply induction_map_even_tensor
  exact he.1

theorem contentEPairComparison_outer_tensor
    (τ : List I) (γ : Multiset I) (hγ : δ₂ + (τ : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N δ₁) (z : ContentCategory D Sc cutoff N δ₂)
    (t : ContentCategory D Sc cutoff N γ)
    (g : (contentAppendTo D Sc cutoff N δ₂ τ γ hγ).obj z ⟶ t)
    (b : (K).obj w ⟶ z) (a : (J).obj v ⟶ w) (m : M.obj v) :
    ((BalancedInduction.induction (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)).map
      ((contentEPairComparison D Sc cutoff N β i j).hom.app M)).total t
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)
        (BalancedInduction.induced K (BalancedInduction.induced J M)).toFunctor z g
        (BalancedInduction.tensor K (BalancedInduction.induced J M).toFunctor w b
          (BalancedInduction.tensor J M.toFunctor v a m))) =
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)
      (BalancedInduction.induced A M).toFunctor z g
      (BalancedInduction.tensor A M.toFunctor v
        (eqToHom (congrArg (fun F => F.obj v) e).symm ≫ (K).map a ≫ b) m) := by
  exact (contentEPairComparison_outer_apply D Sc cutoff N β i j τ γ hγ M z t g
    (BalancedInduction.tensor K (BalancedInduction.induced J M).toFunctor w b
      (BalancedInduction.tensor J M.toFunctor v a m))).trans (congrArg
    (BalancedInduction.tensor (contentAppendTo D Sc cutoff N δ₂ τ γ hγ)
      (BalancedInduction.induced A M).toFunctor z g)
    (contentEPairComparison_hom_total_tensor D Sc cutoff N β i j M v w z b a m))

/-- Flatten the pair-first composition tree; taking `τ = [l]` gives its triple leg. -/
theorem contentEPairComparison_comp_tensor
    (τ : List I) (γ : Multiset I) (hγ : δ₂ + (τ : Multiset I) = γ)
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
    BalancedInduction.tensor (contentAppendTo D Sc cutoff N β ([i,j] ++ τ) γ h)
      M.toFunctor v
      (eqToHom (congrArg (fun F => F.obj v)
        (contentAppend_compTo_eq D Sc cutoff N β [i,j] δ₂ (contentPair_sum β i j)
          τ γ hγ h)).symm ≫
        (contentAppendTo D Sc cutoff N δ₂ τ γ hγ).map
          (eqToHom (congrArg (fun F => F.obj v) e).symm ≫ (K).map a ≫ b) ≫ g) m := by
  have hw := contentEPairComparison_outer_tensor D Sc cutoff N β i j τ γ hγ M v w z t g b a m
  refine (congrArg
    (((contentInductionCompTo D Sc cutoff N β [i,j] δ₂ (contentPair_sum β i j)
      τ γ hγ h).hom.app M).total t) hw).trans ?_
  apply contentInductionCompTo_hom_total_tensor
end Pair
end OddMath.QuiverHecke.ELVOld
