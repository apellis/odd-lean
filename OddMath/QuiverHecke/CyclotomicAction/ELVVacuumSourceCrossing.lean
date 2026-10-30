import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSourceComparison
/-! # Normalized crossing in iterated source coordinates

The canonical pair comparison is computed in `ELVVacuumSourceComparison`.
`pairCross_mixed_coordinates` computes the existing `contentEPairCross`, not a
newly chosen conjugate: both its input and output use successive representable
evaluations. This supplies the pair-source calculation for vacuum observations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.VacuumSourceComparison
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
theorem flatten_cross (β : Multiset I) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ) :
    (contentEPairEquiv D Sc cutoff N β i j γ hij M w).toLinearMap ∘ₗ
      contentEPairCross D Sc cutoff N β i j γ hij hji M w =
    BalancedInduction.transformLinear
      (contentAppendTo_supernatural D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j)) M w ∘ₗ
      (contentEPairEquiv D Sc cutoff N β j i γ hji M w).toLinearMap := by
  unfold contentEPairCross
  exact LinearEquiv.comp_symm_assoc _

/-- The actual transported pair crossing, with both source and output in
successive representable coordinates. -/
theorem pairCross_coordinates (β : Multiset I) (i j : I) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (v : ContentCategory D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ)
    (x : ContentEPairSpace D Sc cutoff N β j i γ hji (contentRepresentable D Sc cutoff N β v) w) :
    pairCoordinates D Sc cutoff N β i j γ hij v w
      (contentEPairCross D Sc cutoff N β i j γ hij hji (contentRepresentable D Sc cutoff N β v) w x) =
      contentAppendToComponent D Sc cutoff N hij hji (contentCrossAffine D Sc i j) v ≫
        twist k (D.parity i * D.parity j) (pairCoordinates D Sc cutoff N β j i γ hji v w x) := by
  rw [pairCoordinates_comparison, pairCoordinates_comparison]
  have hf := congrArg (fun f => f x)
    (flatten_cross D Sc cutoff N β i j γ hij hji (contentRepresentable D Sc cutoff N β v) w)
  change contentEPairEquiv D Sc cutoff N β i j γ hij (contentRepresentable D Sc cutoff N β v) w
    (contentEPairCross D Sc cutoff N β i j γ hij hji (contentRepresentable D Sc cutoff N β v) w x) = _ at hf
  rw [hf]
  suffices he : ∀ y : BalancedInduction.Obj (contentAppendTo D Sc cutoff N β [j,i] γ hji)
      (contentRepresentableFunctor D Sc cutoff N β v) w,
      VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [i,j] γ hij v w
        (BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j))
          (contentRepresentable D Sc cutoff N β v) w y) =
        contentAppendToComponent D Sc cutoff N hij hji (contentCrossAffine D Sc i j) v ≫
          twist k (D.parity i * D.parity j)
            (VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [j,i] γ hji v w y) by
    exact he _
  intro y
  obtain ⟨a, rfl⟩ := (VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [j,i] γ hji v w).symm.surjective y
  rw [LinearEquiv.apply_symm_apply, VacuumGeneratorCoordinates.equivTo_symm]
  have ht := BalancedInduction.transformLinear_tensor
    (contentAppendTo_supernatural D Sc cutoff N hij hji (contentCrossAffine_mem D Sc i j))
    (contentRepresentable D Sc cutoff N β v) w v a (𝟙 v)
  refine (congrArg (VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [i,j] γ hij v w) ht).trans ?_
  exact (VacuumGeneratorCoordinates.equivTo_tensor D Sc cutoff N β [i,j] γ hij v v w
    (contentAppendToComponent D Sc cutoff N hij hji (contentCrossAffine D Sc i j) v ≫
      twist k (D.parity i * D.parity j) a) (𝟙 v)).trans
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp])

theorem pairCross_mixed_coordinates (β : Multiset I) (i j : I) (hne : i ≠ j) (γ : Multiset I)
    (hij : β + ([i,j] : Multiset I) = γ) (hji : β + ([j,i] : Multiset I) = γ)
    (v : ContentCategory D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ)
    (x : ContentEPairSpace D Sc cutoff N β j i γ hji (contentRepresentable D Sc cutoff N β v) w) :
    pairCoordinates D Sc cutoff N β i j γ hij v w
      (contentEPairCross D Sc cutoff N β i j γ hij hji (contentRepresentable D Sc cutoff N β v) w x) =
      contentAppendToComponent D Sc cutoff N hij hji (crossTwo D Sc i j) v ≫
        twist k (D.parity i * D.parity j) (pairCoordinates D Sc cutoff N β j i γ hji v w x) := by
  rw [pairCross_coordinates, contentCrossAffine_distinct D Sc i j hne]

end OddMath.QuiverHecke.ELVOld.VacuumSourceComparison
