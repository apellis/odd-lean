import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedKernelClosureCoordinates

/-! # Weighted kernel closure evaluation at arbitrary stored content

The G8 coefficient attachment retains arbitrary stored content and evaluates
the literal weighted local closure by the truncated raw kernel coefficient.
-/
noncomputable section
set_option backward.dsimp.instances true
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i : I)
  (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k))
local notation "RM" => weightedRestriction D Sc cutoff N M

private theorem restriction_map_value (v t : OldCategory D Sc cutoff) (f : v ⟶ t)
    (b : (RM).obj v) :
    (RM).map f b = M.map ((oldTruncateFunctor D Sc cutoff N).map f) b := rfl
private theorem quotient_map_value (v t : OldCategory D Sc cutoff) (f : v ⟶ t) :
    (oldTruncateFunctor D Sc cutoff N).map f =
      truncateOld D Sc cutoff N v.word t.word f := rfl

private theorem content_induction
    {P : ∀ β : Multiset I, ContentCategory D Sc cutoff N β → Prop}
    (h : ∀ t : OldCategory D Sc cutoff,
      P (t.word : Multiset I) ⟨(oldTruncateFunctor D Sc cutoff N).obj t, rfl⟩)
    (β : Multiset I) (w : ContentCategory D Sc cutoff N β) : P β w := by
  rcases w with ⟨t, ht⟩
  cases ht
  exact h ⟨t.word⟩

attribute [local irreducible] positiveKernelClosure negativeKernelClosure
  weightedContentUnitClosureValue weightedContentCapClosureValue

/-- The specified unit closure is the action of its original raw coefficient. -/
theorem weightedContentUnitClosureValue_evaluate (β : Multiset I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i β) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) (b : M.obj w.obj) :
    weightedContentUnitClosureValue D Sc cutoff N i M β hh w r s b =
    M.map (truncateOld D Sc cutoff N w.obj.word w.obj.word
      (positiveKernelClosure D Sc cutoff i ⟨w.obj.word⟩ ⟨w.obj.word⟩
        (by rw [w.content]; exact hh) r s
        (𝟙 (⟨w.obj.word⟩ : OldCategory D Sc cutoff)))) b := by
  revert hh r s b
  refine content_induction D Sc cutoff N (P := fun β₀ w₀ =>
    ∀ (hh : 0 ≤ contentCrossingHeight D cutoff i β₀) (r s : ℕ) (b : M.obj w₀.obj),
      weightedContentUnitClosureValue D Sc cutoff N i M β₀ hh w₀ r s b =
      M.map (truncateOld D Sc cutoff N w₀.obj.word w₀.obj.word
        (positiveKernelClosure D Sc cutoff i ⟨w₀.obj.word⟩ ⟨w₀.obj.word⟩
          (by rw [w₀.content]; exact hh) r s
          (𝟙 (⟨w₀.obj.word⟩ : OldCategory D Sc cutoff)))) b) ?_ β w
  intro t hh r s b
  have h := weightedContentUnitClosureValue_atWord D Sc cutoff N i M t hh r s b
  rw [restriction_map_value, quotient_map_value] at h
  exact h

/-- The specified cap closure retains the same raw coefficient at arbitrary content. -/
theorem weightedContentCapClosureValue_evaluate (β : Multiset I)
    (hh : contentCrossingHeight D cutoff i β ≤ 0) (w : ContentCategory D Sc cutoff N β)
    (r s : ℕ) (b : M.obj w.obj) :
    weightedContentCapClosureValue D Sc cutoff N i M β hh w r s b =
    M.map (truncateOld D Sc cutoff N w.obj.word w.obj.word
      (negativeKernelClosure D Sc cutoff i ⟨w.obj.word⟩ ⟨w.obj.word⟩
        (by rw [w.content]; exact hh) r s
        (𝟙 (⟨w.obj.word⟩ : OldCategory D Sc cutoff)))) b := by
  revert hh r s b
  refine content_induction D Sc cutoff N (P := fun β₀ w₀ =>
    ∀ (hh : contentCrossingHeight D cutoff i β₀ ≤ 0) (r s : ℕ) (b : M.obj w₀.obj),
      weightedContentCapClosureValue D Sc cutoff N i M β₀ hh w₀ r s b =
      M.map (truncateOld D Sc cutoff N w₀.obj.word w₀.obj.word
        (negativeKernelClosure D Sc cutoff i ⟨w₀.obj.word⟩ ⟨w₀.obj.word⟩
          (by rw [w₀.content]; exact hh) r s
          (𝟙 (⟨w₀.obj.word⟩ : OldCategory D Sc cutoff)))) b) ?_ β w
  intro t hh r s b
  have h := weightedContentCapClosureValue_atWord D Sc cutoff N i M t hh r s b
  rw [restriction_map_value, quotient_map_value] at h
  exact h

end OddMath.QuiverHecke.ELVOld
