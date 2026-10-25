import OddMath.SKM.PairedTargetIndependence

/-! Coordinates of the unpaired target sector modulo the complete paired
sector. Coordinates are obtained only from an assumed independent swapped
matching family. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}
namespace SameColourTargetFrame
variable {cs : CScalars Sc} {μ : X} {a P Q : List (Letter I)} {i : I}
  (F : SameColourTargetFrame cs μ a P Q i)

def swappedCoordinates (hG : Function.Injective (F.swapped.expansion cs μ)) :
    ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ (P ++ dn i :: up i :: Q))) ≃ₗ[k]
      (F.swapped.Labels →₀ SYM D k) :=
  (LinearEquiv.ofBijective (F.swapped.expansion cs μ)
    ⟨hG, F.swapped.expansion_surjective cs μ⟩).symm

@[simp] theorem swappedCoordinates_expansion
    (hG : Function.Injective (F.swapped.expansion cs μ)) (v : F.swapped.Labels →₀ SYM D k) :
    F.swappedCoordinates hG (F.swapped.expansion cs μ v) = v :=
  (LinearEquiv.ofBijective (F.swapped.expansion cs μ)
    ⟨hG, F.swapped.expansion_surjective cs μ⟩).symm_apply_apply v

theorem pairedRowsInclusion_off (v : (F.residual.Labels × ℕ) →₀ SYM D k)
    (t : F.original.Labels) (ht : t ∉ Set.range F.paired) :
    F.residual.pairedRowsInclusion (D := D) (k := k) i F.swapped F.swappedPaired v (F.exchange t) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨⟨r, b⟩, he⟩
  apply ht
  exact ⟨(b, r), F.exchange.injective he⟩

/-- Every native residual morphism followed by a cup is invisible at an
unpaired coordinate, including arbitrary residual SYM coefficients. -/
theorem swappedCoordinates_cup_off
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (f : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ (P ++ Q)))
    (b : ℕ) (t : F.original.Labels) (ht : t ∉ Set.range F.paired) :
    F.swappedCoordinates hG
      (f ≫ MatchingBasisChoice.targetCupRows (Sc := Sc) μ P Q i b) (F.exchange t) = 0 := by
  obtain ⟨v, rfl⟩ := F.residual.expansion_surjective cs μ f
  have H := F.residual.pairedRowsInclusion_eval cs μ i F.swapped F.swappedPaired
    F.swapped_row (F.residual.residualRow b v)
  rw [F.residual.postRowsExpansion_residualRow] at H
  rw [← H, F.swappedCoordinates_expansion]
  exact F.pairedRowsInclusion_off _ t ht

/-- Paired input columns have no unpaired principal coordinates at any height. -/
theorem swappedCoordinates_paired_cross_off
    (hG : Function.Injective (F.swapped.expansion cs μ)) (b : ℕ)
    (r : F.residual.Labels) (d : SYM D k) (t : F.original.Labels)
    (ht : t ∉ Set.range F.paired) :
    F.swappedCoordinates hG
      (F.original.expansion cs μ (Finsupp.single (F.paired (b, r)) d) ≫
        sameColourTargetCross (Sc := Sc) μ P Q i) (F.exchange t) = 0 := by
  by_cases hh : 0 < D.h i (wt D μ Q)
  · let N := (D.h i (wt D μ Q)).toNat
    have hN : D.h i (wt D μ Q) = (N : ℤ) := by dsimp [N]; omega
    rw [← F.positive_column N b r d hN (by omega), F.swappedCoordinates_expansion]
    exact F.pairedRowsInclusion_off _ t ht
  · let N := (-D.h i (wt D μ Q)).toNat
    have hN : -D.h i (wt D μ Q) = (N : ℤ) := by dsimp [N]; omega
    rw [← F.nonpositive_column N b r d hN, F.swappedCoordinates_expansion]
    exact F.pairedRowsInclusion_off _ t ht

end SameColourTargetFrame
end OddMath.SKM
