import OddMath.SKM.PairedSourceColumns

/-! Unpaired source coordinates with the full parity twist. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

theorem sourcePlcW_comp_at (μ : X) (s t mid u v a b c : List (Letter I))
    (hm : mid = u ++ b ++ v)
    (g₁ : (pres D Sc).obj (ob D (wt D μ v) a) ⟶ (pres D Sc).obj (ob D (wt D μ v) b))
    (g₂ : (pres D Sc).obj (ob D (wt D μ v) b) ⟶ (pres D Sc).obj (ob D (wt D μ v) c)) :
    plcW μ s mid u v a b g₁ ≫ plcW μ mid t u v b c g₂ =
      plcW μ s t u v a c (g₁ ≫ g₂) := by
  subst mid
  exact (plcW_comp μ s t u v a b c g₁ g₂).symm

private theorem sourcePlcW_id (μ : X) (mid P Q b : List (Letter I))
    (hm : mid = P ++ b ++ Q) :
    plcW (D := D) (Sc := Sc) μ mid mid P Q b b (𝟙 _) = 𝟙 _ := by
  subst mid
  simp only [plcW_apply, plcL_id, cl_nil, Category.id_comp]

def sameColourSourceCross (μ : X) (P Q : List (Letter I)) (i : I) :
    (pres D Sc).obj (ob D μ (P ++ up i :: dn i :: Q)) ⟶
      (pres D Sc).obj (ob D μ (P ++ dn i :: up i :: Q)) :=
  plcW μ (P ++ up i :: dn i :: Q) (P ++ dn i :: up i :: Q) P Q
    [up i, dn i] [dn i, up i] (sgM D Sc i (wt D μ Q))

def sameColourSourceReverseCross (μ : X) (P Q : List (Letter I)) (i : I) :
    (pres D Sc).obj (ob D μ (P ++ dn i :: up i :: Q)) ⟶
      (pres D Sc).obj (ob D μ (P ++ up i :: dn i :: Q)) :=
  plcW μ (P ++ dn i :: up i :: Q) (P ++ up i :: dn i :: Q) P Q
    [dn i, up i] [up i, dn i] (lcM D Sc i (wt D μ Q))

theorem sameColourSourceCross_eval (cs : CScalars Sc) (μ : X) (P Q : List (Letter I)) (i : I) :
    xev cs μ (P ++ up i :: dn i :: Q) (P ++ dn i :: up i :: Q)
      ((xCrL (up i) (dn i)).map (xwhL P Q)) = sameColourSourceCross (Sc := Sc) μ P Q i := by
  rw [xev_eq_plcW (cs := cs) μ P Q (xChain_xCrL (up i) (dn i)) (xCrL_ne_nil _ _)]
  change plcW _ _ _ _ _ _ _ (xev cs _ _ _ ((sigmaL i i).map ofL)) = _
  rw [xev_map_ofL]
  rfl

theorem sameColourSourceReverseCross_eval (cs : CScalars Sc) (μ : X)
    (P Q : List (Letter I)) (i : I) :
    xev cs μ (P ++ dn i :: up i :: Q) (P ++ up i :: dn i :: Q)
      ((xCrL (dn i) (up i)).map (xwhL P Q)) = sameColourSourceReverseCross (Sc := Sc) μ P Q i := by
  rw [xev_eq_plcW (cs := cs) μ P Q (xChain_xCrL (dn i) (up i)) (xCrL_ne_nil _ _)]
  change plcW _ _ _ _ _ _ _ (xev cs _ _ _ ((lcrossL i i).map ofL)) = _
  rw [xev_map_ofL]
  rfl

theorem sameColourSourceCross_mem_parity (μ : X) (P Q : List (Letter I)) (i : I) :
    sameColourSourceCross (Sc := Sc) μ P Q i ∈
      homPar D Sc μ (P ++ up i :: dn i :: Q) (P ++ dn i :: up i :: Q) (D.parity i) := by
  have H : sameColourSourceCross (Sc := Sc) μ P Q i =
      cl D Sc μ (P ++ up i :: dn i :: Q) (P ++ dn i :: up i :: Q)
        ((sigmaL i i).map (whL P Q)) := by
    simp only [sameColourSourceCross, sgM, plcW_apply, plcL_cl]
    exact cl_cast _ (by simp) (by simp)
  rw [H]
  simpa only [parsum_map_whL, parsum_sigmaL, zmod2_mul_self] using
    cl_mem_homPar' (D := D) (Sc := Sc) μ (P ++ up i :: dn i :: Q)
      (P ++ dn i :: up i :: Q) ((sigmaL i i).map (whL P Q))

theorem sameColourSourceCross_rightAction (cs : CScalars Sc) (μ : X)
    (P Q Z : List (Letter I)) (i : I)
    (f : (pres D Sc).obj (ob D μ (P ++ dn i :: up i :: Q)) ⟶ (pres D Sc).obj (ob D μ Z))
    (d : SYM D k) :
    sameColourSourceCross (Sc := Sc) μ P Q i ≫ MatchingBasisChoice.rightAction cs μ f d =
      MatchingBasisChoice.rightAction cs μ (sameColourSourceCross (Sc := Sc) μ P Q i ≫ f)
        (SYM.parityTwist D k (D.parity i) d) := by
  dsimp only [MatchingBasisChoice.rightAction]
  rw [← Category.assoc, ← source_target_twist cs μ (sameColourSourceCross_mem_parity μ P Q i),
    Category.assoc]

theorem sameColourSourceCross_reverse (μ : X) (P Q : List (Letter I)) (i : I) :
    sameColourSourceCross (Sc := Sc) μ P Q i ≫ sameColourSourceReverseCross μ P Q i =
      (∑ n ∈ Finset.range (D.h i (wt D μ Q)).toNat,
        sourceCapRows (Sc := Sc) μ P Q i n ≫
          plcW μ (P ++ Q) (P ++ up i :: dn i :: Q) P Q [] [up i, dn i]
            (dcM D Sc i (wt D μ Q) n)) - 𝟙 _ := by
  rw [sameColourSourceCross, sameColourSourceReverseCross,
    sourcePlcW_comp_at μ _ _ _ P Q [up i, dn i] [dn i, up i] [up i, dn i] (by simp),
    sg_lc i (wt D μ Q), map_sub, map_sum,
    sourcePlcW_id μ _ P Q [up i, dn i] (by simp)]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact (sourcePlcW_comp_at μ _ _ (P ++ Q) P Q [up i, dn i] [] [up i, dn i]
    (by simp) (eLM D Sc i (wt D μ Q) n) (dcM D Sc i (wt D μ Q) n)).symm

namespace SameColourSourceFrame
variable {P Q Z : List (Letter I)} {i : I} (F : SameColourSourceFrame P Q Z i)
  {cs : CScalars Sc} {μ : X}

def swappedCoordinates (hG : Function.Injective (F.swapped.expansion cs μ)) :
    ((pres D Sc).obj (ob D μ (P ++ up i :: dn i :: Q)) ⟶ (pres D Sc).obj (ob D μ Z)) ≃ₗ[k]
      (F.swapped.Labels →₀ SYM D k) :=
  (LinearEquiv.ofBijective (F.swapped.expansion cs μ)
    ⟨hG, F.swapped.expansion_surjective cs μ⟩).symm

@[simp] theorem swappedCoordinates_expansion
    (hG : Function.Injective (F.swapped.expansion cs μ)) (v : F.swapped.Labels →₀ SYM D k) :
    F.swappedCoordinates hG (F.swapped.expansion cs μ v) = v :=
  (LinearEquiv.ofBijective (F.swapped.expansion cs μ)
    ⟨hG, F.swapped.expansion_surjective cs μ⟩).symm_apply_apply v

theorem swappedPairedInclusion_off (v : (F.residual.Labels × ℕ) →₀ SYM D k)
    (t : F.original.Labels) (ht : t ∉ Set.range F.paired) :
    F.swappedPairedInclusion v (F.exchange t) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨⟨r, b⟩, he⟩
  exact ht ⟨(b, r), F.exchange.injective he⟩

/-- Native caps with arbitrary residual morphisms have only paired coordinates.
The residual coefficients are transported using the cap's own parity. -/
theorem swappedCoordinates_cap_off
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (f : (pres D Sc).obj (ob D μ (P ++ Q)) ⟶ (pres D Sc).obj (ob D μ Z))
    (m : ℕ) (t : F.original.Labels) (ht : t ∉ Set.range F.paired) :
    F.swappedCoordinates hG (sourceCapRows (Sc := Sc) μ P Q i m ≫ f) (F.exchange t) = 0 := by
  obtain ⟨v, rfl⟩ := F.residual.expansion_surjective cs μ f
  have H := F.swappedPairedInclusion_eval cs μ (F.capResidualColumn m v)
  rw [capResidualColumn, F.residual.preRowsExpansion_residualRow cs μ _ m _
    (sourceCapRows_mem_parity μ P Q i m)] at H
  rw [← H, F.swappedCoordinates_expansion]
  exact F.swappedPairedInclusion_off _ t ht

theorem swappedCoordinates_cap_rightAction_off
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (f : (pres D Sc).obj (ob D μ (P ++ Q)) ⟶ (pres D Sc).obj (ob D μ Z))
    (m : ℕ) (d : SYM D k) (t : F.original.Labels) (ht : t ∉ Set.range F.paired) :
    F.swappedCoordinates hG
      (MatchingBasisChoice.rightAction cs μ (sourceCapRows (Sc := Sc) μ P Q i m ≫ f) d)
        (F.exchange t) = 0 := by
  obtain ⟨v, rfl⟩ := F.residual.expansion_surjective cs μ f
  have H := F.capResidualColumn_eval cs μ m v 0 d
  simp only [sourceParityTwist_zero, LinearMap.id_apply] at H
  rw [← H, F.swappedCoordinates_expansion]
  exact F.swappedPairedInclusion_off _ t ht

theorem swappedCoordinates_reverse_cross
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (f : (pres D Sc).obj (ob D μ (P ++ up i :: dn i :: Q)) ⟶ (pres D Sc).obj (ob D μ Z))
    (d : SYM D k) (t : F.original.Labels) (ht : t ∉ Set.range F.paired) :
    F.swappedCoordinates hG (MatchingBasisChoice.rightAction cs μ
      (sameColourSourceCross (Sc := Sc) μ P Q i ≫ sameColourSourceReverseCross μ P Q i ≫ f) d)
        (F.exchange t) =
      -(F.swappedCoordinates hG (MatchingBasisChoice.rightAction cs μ f d) (F.exchange t)) := by
  rw [← Category.assoc, sameColourSourceCross_reverse,
    Preadditive.sub_comp, Preadditive.sum_comp, Category.id_comp]
  simp only [MatchingBasisChoice.rightAction, Preadditive.comp_sub, Preadditive.comp_sum,
    map_sub, map_sum, Finsupp.sub_apply, Finsupp.finsetSum_apply, Category.assoc]
  suffices H : (∑ n ∈ Finset.range (D.h i (wt D μ Q)).toNat,
    F.swappedCoordinates hG (MatchingBasisChoice.rightAction cs μ
      (sourceCapRows (Sc := Sc) μ P Q i n ≫
        (plcW μ (P ++ Q) (P ++ up i :: dn i :: Q) P Q [] [up i, dn i]
          (dcM D Sc i (wt D μ Q) n) ≫ f)) d) (F.exchange t)) = 0 by
    dsimp only [MatchingBasisChoice.rightAction] at H
    rw [H, zero_sub]
  apply Finset.sum_eq_zero
  intro n _
  exact F.swappedCoordinates_cap_rightAction_off hG _ n d t ht

/-- Unpaired input columns have a signed full-SYM parity-twisted diagonal,
modulo the actual paired cap sector. -/
theorem swappedCoordinates_unpaired_cross
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (s t : F.original.Labels) (hs : s ∉ Set.range F.paired) (ht : t ∉ Set.range F.paired)
    (d : SYM D k) :
    F.swappedCoordinates hG
      (sameColourSourceCross (Sc := Sc) μ P Q i ≫ F.original.expansion cs μ (Finsupp.single s d))
        (F.exchange t) = Finsupp.single (F.exchange s) (SYM.parityTwist D k (D.parity i) d) (F.exchange t) ∨
    F.swappedCoordinates hG
      (sameColourSourceCross (Sc := Sc) μ P Q i ≫ F.original.expansion cs μ (Finsupp.single s d))
        (F.exchange t) = -Finsupp.single (F.exchange s) (SYM.parityTwist D k (D.parity i) d) (F.exchange t) := by
  have hc : XChain (P ++ up i :: dn i :: Q)
      ((xCrL (up i) (dn i)).map (xwhL P Q)) (P ++ dn i :: up i :: Q) := by
    simpa [List.append_assoc] using (xChain_xCrL (up i) (dn i)).whisk P Q
  have hr : XChain (P ++ dn i :: up i :: Q)
      ((xCrL (dn i) (up i)).map (xwhL P Q)) (P ++ up i :: dn i :: Q) := by
    simpa [List.append_assoc] using (xChain_xCrL (dn i) (up i)).whisk P Q
  rcases F.unpaired s hs with hl | hh
  · left
    have H : sameColourSourceCross (Sc := Sc) μ P Q i ≫
        F.original.expansion cs μ (Finsupp.single s d) =
        F.swapped.expansion cs μ (Finsupp.single (F.exchange s)
          (SYM.parityTwist D k (D.parity i) d)) := by
      rw [F.original.source_expansion_single, sameColourSourceCross_rightAction,
        F.swapped.source_expansion_single, hl, xev_append cs _ hc, sameColourSourceCross_eval]
    rw [H, F.swappedCoordinates_expansion]
  · right
    rw [F.original.source_expansion_single, hh, xev_append cs _ hr, sameColourSourceReverseCross_eval,
      sameColourSourceCross_rightAction, F.swappedCoordinates_reverse_cross hG _ _ t ht]
    rw [← F.swapped.source_expansion_single, F.swappedCoordinates_expansion]

end SameColourSourceFrame
end OddMath.SKM
