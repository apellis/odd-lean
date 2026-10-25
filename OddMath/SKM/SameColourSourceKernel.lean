import OddMath.SKM.PairedSourceSupport

/-! Full source kernel support, without restricting SYM coefficients to a
homogeneous piece. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}
namespace SameColourSourceFrame
variable {cs : CScalars Sc} {μ : X} {P Q Z : List (Letter I)} {i : I}
  (F : SameColourSourceFrame P Q Z i)

def principalCoordinates (hG : Function.Injective (F.swapped.expansion cs μ)) :
    (F.original.Labels →₀ SYM D k) →ₗ[k] (F.swapped.Labels →₀ SYM D k) where
  toFun v := F.swappedCoordinates hG
    (sameColourSourceCross (Sc := Sc) μ P Q i ≫ F.original.expansion cs μ v)
  map_add' v w := by rw [map_add, Preadditive.comp_add, map_add]
  map_smul' c v := by rw [map_smul, Linear.comp_smul, map_smul]; rfl

private theorem principalCoordinates_off
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (s t : F.original.Labels) (ht : t ∉ Set.range F.paired) (hst : s ≠ t) (d : SYM D k) :
    F.principalCoordinates hG (Finsupp.single s d) (F.exchange t) = 0 := by
  classical
  by_cases hs : s ∈ Set.range F.paired
  · obtain ⟨⟨b, r⟩, rfl⟩ := hs
    exact F.swappedCoordinates_paired_cross_off hG b r d t ht
  · rcases F.swappedCoordinates_unpaired_cross hG s t hs ht d with H | H
    · simpa [principalCoordinates, F.exchange.injective.ne hst] using H
    · simpa [principalCoordinates, F.exchange.injective.ne hst] using H

private theorem principalCoordinates_diagonal
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (t : F.original.Labels) (ht : t ∉ Set.range F.paired) (d : SYM D k) :
    F.principalCoordinates hG (Finsupp.single t d) (F.exchange t) =
        SYM.parityTwist D k (D.parity i) d ∨
      F.principalCoordinates hG (Finsupp.single t d) (F.exchange t) =
        -SYM.parityTwist D k (D.parity i) d := by
  simpa [principalCoordinates] using F.swappedCoordinates_unpaired_cross hG t t ht ht d

/-- A relation among the complete original source family has only paired
support. The signed diagonal is a full coefficient involution, not a scalar
sign on arbitrary inhomogeneous coefficients. -/
theorem kernel_supported_paired
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (f : F.original.Labels →₀ SYM D k) (hf : F.original.expansion cs μ f = 0)
    (t : F.original.Labels) (ht : t ∉ Set.range F.paired) : f t = 0 := by
  classical
  have proj (v : F.original.Labels →₀ SYM D k) :
      F.principalCoordinates hG v (F.exchange t) =
        F.principalCoordinates hG (Finsupp.single t (v t)) (F.exchange t) := by
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw =>
      simp only [map_add, Finsupp.add_apply, Finsupp.single_add, hv, hw]
    | single s d =>
      by_cases hst : s = t
      · subst s; simp
      · rw [F.principalCoordinates_off hG s t ht hst d]
        simp [Ne.symm hst]
  have hz : F.principalCoordinates hG (Finsupp.single t (f t)) (F.exchange t) = 0 := by
    rw [← proj]
    simp [principalCoordinates, hf]
  have he : SYM.parityTwist D k (D.parity i) (f t) = 0 := by
    rcases F.principalCoordinates_diagonal hG t ht (f t) with H | H
    · exact H.symm.trans hz
    · exact neg_eq_zero.mp (H.symm.trans hz)
  have H := congrArg (SYM.parityTwist D k (D.parity i)) he
  simpa only [SYM.parityTwist_involutive, map_zero] using H

#print axioms kernel_supported_paired
end SameColourSourceFrame
end OddMath.SKM
