import OddMath.SKM.SameColourTargetCoordinates

/-! Native same-colour inverse crossings modulo paired target cup rows. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

theorem plcW_id_at (μ : X) (mid P Q b : List (Letter I)) (hm : mid = P ++ b ++ Q) :
    plcW (D := D) (Sc := Sc) μ mid mid P Q b b (𝟙 _) = 𝟙 _ := by
  subst mid
  simp only [plcW_apply, plcL_id, cl_nil, Category.id_comp]

def sameColourReverseCross (μ : X) (P Q : List (Letter I)) (i : I) :
    (pres D Sc).obj (ob D μ (P ++ dn i :: up i :: Q)) ⟶
      (pres D Sc).obj (ob D μ (P ++ up i :: dn i :: Q)) :=
  plcW μ (P ++ dn i :: up i :: Q) (P ++ up i :: dn i :: Q) P Q
    [dn i, up i] [up i, dn i] (lcM D Sc i (wt D μ Q))

theorem sameColourTargetCross_eval (cs : CScalars Sc) (μ : X) (P Q : List (Letter I)) (i : I) :
    xev cs μ (P ++ up i :: dn i :: Q) (P ++ dn i :: up i :: Q)
      ((xCrL (up i) (dn i)).map (xwhL P Q)) = sameColourTargetCross (Sc := Sc) μ P Q i := by
  rw [xev_eq_plcW (cs := cs) μ P Q (xChain_xCrL (up i) (dn i)) (xCrL_ne_nil _ _)]
  change plcW _ _ _ _ _ _ _ (xev cs _ _ _ ((sigmaL i i).map ofL)) = _
  rw [xev_map_ofL]
  rfl

theorem sameColourReverseCross_eval (cs : CScalars Sc) (μ : X) (P Q : List (Letter I)) (i : I) :
    xev cs μ (P ++ dn i :: up i :: Q) (P ++ up i :: dn i :: Q)
      ((xCrL (dn i) (up i)).map (xwhL P Q)) = sameColourReverseCross (Sc := Sc) μ P Q i := by
  rw [xev_eq_plcW (cs := cs) μ P Q (xChain_xCrL (dn i) (up i)) (xCrL_ne_nil _ _)]
  change plcW _ _ _ _ _ _ _ (xev cs _ _ _ ((lcrossL i i).map ofL)) = _
  rw [xev_map_ofL]
  rfl

theorem sameColourReverseCross_target_nonneg (μ : X) (P Q : List (Letter I)) (i : I)
    (hh : 0 ≤ D.h i (wt D μ Q)) :
    sameColourReverseCross (Sc := Sc) μ P Q i ≫ sameColourTargetCross μ P Q i = -𝟙 _ := by
  rw [sameColourReverseCross, sameColourTargetCross,
    plcW_comp_at μ _ _ _ P Q [dn i, up i] [up i, dn i] [dn i, up i] (by simp),
    lc_sg i (wt D μ Q) hh, map_neg, plcW_id_at μ _ P Q [dn i, up i] (by simp)]

theorem sameColourReverseCross_target_nonpos (μ : X) (P Q : List (Letter I)) (i : I)
    (hh : D.h i (wt D μ Q) ≤ 0) :
    sameColourReverseCross (Sc := Sc) μ P Q i ≫ sameColourTargetCross μ P Q i =
      (∑ n ∈ Finset.range (-D.h i (wt D μ Q)).toNat,
        plcW μ (P ++ dn i :: up i :: Q) (P ++ Q) P Q [dn i, up i] []
          (dkM D Sc i (wt D μ Q) n) ≫ MatchingBasisChoice.targetCupRows (Sc := Sc) μ P Q i n) - 𝟙 _ := by
  rw [sameColourReverseCross, sameColourTargetCross,
    plcW_comp_at μ _ _ _ P Q [dn i, up i] [up i, dn i] [dn i, up i] (by simp),
    lc_sg_nonpos i (wt D μ Q) hh, map_sub, map_sum,
    plcW_id_at μ _ P Q [dn i, up i] (by simp)]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact (plcW_comp_at μ _ _ (P ++ Q) P Q [dn i, up i] [] [dn i, up i]
    (by simp) (dkM D Sc i (wt D μ Q) n) (hLM D Sc i (wt D μ Q) n)).symm

namespace SameColourTargetFrame
variable {cs : CScalars Sc} {μ : X} {a P Q : List (Letter I)} {i : I}
  (F : SameColourTargetFrame cs μ a P Q i)

theorem swappedCoordinates_reverse_cross
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (f : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ (P ++ dn i :: up i :: Q)))
    (t : F.original.Labels) (ht : t ∉ Set.range F.paired) :
    F.swappedCoordinates hG (f ≫ sameColourReverseCross (Sc := Sc) μ P Q i ≫
      sameColourTargetCross μ P Q i) (F.exchange t) = -(F.swappedCoordinates hG f (F.exchange t)) := by
  by_cases hh : 0 ≤ D.h i (wt D μ Q)
  · rw [sameColourReverseCross_target_nonneg μ P Q i hh, Preadditive.comp_neg,
      Category.comp_id, map_neg, Finsupp.neg_apply]
  · rw [sameColourReverseCross_target_nonpos μ P Q i (by omega),
      Preadditive.comp_sub, Preadditive.comp_sum, Category.comp_id,
      map_sub, map_sum, Finsupp.sub_apply, Finsupp.finsetSum_apply]
    suffices H : (∑ n ∈ Finset.range (-D.h i (wt D μ Q)).toNat,
      F.swappedCoordinates hG (f ≫
        plcW μ (P ++ dn i :: up i :: Q) (P ++ Q) P Q [dn i, up i] []
          (dkM D Sc i (wt D μ Q) n) ≫ MatchingBasisChoice.targetCupRows (Sc := Sc) μ P Q i n)
            (F.exchange t)) = 0 by rw [H, zero_sub]
    apply Finset.sum_eq_zero
    intro n _
    rw [← Category.assoc]
    exact F.swappedCoordinates_cup_off hG _ n t ht

/-- Each unpaired column is a unit diagonal modulo paired rows, at every
height and for every abstract coefficient, including in nonempty contexts. -/
theorem swappedCoordinates_unpaired_cross
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (s t : F.original.Labels) (hs : s ∉ Set.range F.paired) (ht : t ∉ Set.range F.paired)
    (d : SYM D k) :
    F.swappedCoordinates hG
      (F.original.expansion cs μ (Finsupp.single s d) ≫ sameColourTargetCross (Sc := Sc) μ P Q i)
        (F.exchange t) = Finsupp.single (F.exchange s) d (F.exchange t) ∨
    F.swappedCoordinates hG
      (F.original.expansion cs μ (Finsupp.single s d) ≫ sameColourTargetCross (Sc := Sc) μ P Q i)
        (F.exchange t) = -Finsupp.single (F.exchange s) d (F.exchange t) := by
  rcases F.unpaired s hs with hl | hh
  · left
    have H : F.original.expansion cs μ (Finsupp.single s d) ≫ sameColourTargetCross (Sc := Sc) μ P Q i =
        F.swapped.expansion cs μ (Finsupp.single (F.exchange s) d) := by
      rw [F.original.expansion_single, F.swapped.expansion_single, hl,
        xev_append cs _ (F.original.layers_chain s), sameColourTargetCross_eval, Category.assoc]
    rw [H, F.swappedCoordinates_expansion]
  · right
    have H : F.original.expansion cs μ (Finsupp.single s d) =
        F.swapped.expansion cs μ (Finsupp.single (F.exchange s) d) ≫ sameColourReverseCross (Sc := Sc) μ P Q i := by
      rw [F.original.expansion_single, hh, xev_append cs _ (F.swapped.layers_chain (F.exchange s)),
        sameColourReverseCross_eval, F.swapped.expansion_single, Category.assoc]
    rw [H, Category.assoc, F.swappedCoordinates_reverse_cross hG _ t ht,
      F.swappedCoordinates_expansion]

end SameColourTargetFrame
end OddMath.SKM
