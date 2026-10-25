import OddMath.SKM.SameColourTargetColumns

/-! Complete adapted same-colour target frames, with finite native principal
coefficient columns attached to the very same residual and target choices. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- A complete adapted frame. The residual choice uses the strict serializers
occurring in the evaluated rows, not merely the same underlying matchings. -/
structure SameColourTargetFrame (cs : CScalars Sc) (μ : X)
    (a P Q : List (Letter I)) (i : I) where
  residual : MatchingBasisChoice a (P ++ Q)
  original : MatchingBasisChoice a (P ++ up i :: dn i :: Q)
  swapped : MatchingBasisChoice a (P ++ dn i :: up i :: Q)
  exchange : original.Labels ≃ swapped.Labels
  paired : ℕ × residual.Labels ↪ original.Labels
  unpaired : ∀ t, t ∉ Set.range paired →
    swapped.layers (exchange t) = original.layers t ++ (xCrL (up i) (dn i)).map (xwhL P Q) ∨
    original.layers t = swapped.layers (exchange t) ++ (xCrL (dn i) (up i)).map (xwhL P Q)
  original_row : ∀ b r,
    xev cs μ a (P ++ up i :: dn i :: Q) (original.layers (paired (b, r))) =
      xev cs μ a (P ++ Q) (residual.layers r) ≫
        plcW μ (P ++ Q) (P ++ up i :: dn i :: Q) P Q [] [up i, dn i]
          (etaP cs i (wt D μ Q) ≫ cpow (uLM D Sc i (wt D μ Q)) b)
  swapped_row : ∀ b r,
    xev cs μ a (P ++ dn i :: up i :: Q) (swapped.layers (exchange (paired (b, r)))) =
      xev cs μ a (P ++ Q) (residual.layers r) ≫
        MatchingBasisChoice.targetCupRows (Sc := Sc) μ P Q i b

theorem sameColourTargetFrame_nonempty (cs : CScalars Sc) (μ : X)
    (a P Q : List (Letter I)) (i : I) : Nonempty (SameColourTargetFrame cs μ a P Q i) := by
  obtain ⟨B, F, G, e, p, hu, hF, hG⟩ := exists_same_colour_cup_rows cs μ a P Q i
  exact ⟨⟨B, F, G, e, p, hu, hF, hG⟩⟩

/-- The native target crossing in the displayed boundary contexts. -/
def sameColourTargetCross (μ : X) (P Q : List (Letter I)) (i : I) :
    (pres D Sc).obj (ob D μ (P ++ up i :: dn i :: Q)) ⟶
      (pres D Sc).obj (ob D μ (P ++ dn i :: up i :: Q)) :=
  plcW μ (P ++ up i :: dn i :: Q) (P ++ dn i :: up i :: Q) P Q
    [up i, dn i] [dn i, up i] (sgM D Sc i (wt D μ Q))

namespace SameColourTargetFrame
variable {cs : CScalars Sc} {μ : X} {a P Q : List (Letter I)} {i : I}
  (F : SameColourTargetFrame cs μ a P Q i)

/-- The same paired labels, viewed in the swapped family. -/
def swappedPaired : ℕ × F.residual.Labels ↪ F.swapped.Labels :=
  F.paired.trans F.exchange.toEmbedding

private theorem original_cross (b : ℕ) (r : F.residual.Labels) (d : SYM D k) :
    F.original.expansion cs μ (Finsupp.single (F.paired (b, r)) d) ≫
      sameColourTargetCross (Sc := Sc) μ P Q i =
    MatchingBasisChoice.rightAction cs μ
      (xev cs μ a (P ++ Q) (F.residual.layers r) ≫
        plcW μ (P ++ Q) (P ++ dn i :: up i :: Q) P Q [] [dn i, up i]
          (etaP cs i (wt D μ Q) ≫ cpow (uLM D Sc i (wt D μ Q)) b ≫
            sgM D Sc i (wt D μ Q))) d := by
  rw [F.original.expansion_single, F.original_row]
  have C : cl D Sc μ (P ++ [up i, dn i] ++ Q) (P ++ up i :: dn i :: Q) [] ≫
      cl D Sc μ (P ++ up i :: dn i :: Q) (P ++ [up i, dn i] ++ Q) [] = 𝟙 _ := by
    rw [cl_comp (show SChain (P ++ [up i, dn i] ++ Q) [] (P ++ up i :: dn i :: Q) from by
      change P ++ [up i, dn i] ++ Q = P ++ up i :: dn i :: Q; simp)
      (show SChain (P ++ up i :: dn i :: Q) [] (P ++ [up i, dn i] ++ Q) from by
        change P ++ up i :: dn i :: Q = P ++ [up i, dn i] ++ Q; simp), List.nil_append, cl_nil]
  simp only [MatchingBasisChoice.rightAction, sameColourTargetCross,
    plcW_apply, plcL_comp, Category.assoc]
  rw [← Category.assoc (cl D Sc μ (P ++ [up i, dn i] ++ Q) (P ++ up i :: dn i :: Q) []),
    C, Category.id_comp]

/-- Actual positive-height principal column for every abstract input coefficient. -/
theorem positive_column (N b : ℕ) (r : F.residual.Labels) (d : SYM D k)
    (hN : D.h i (wt D μ Q) = (N : ℤ)) (hpos : 0 < N) :
    F.swapped.expansion cs μ
      (F.residual.pairedRowsInclusion i F.swapped F.swappedPaired
        (MatchingTransition.rightColumn (k := k)
          (F.residual.targetPositiveColumn cs μ i N b r) d)) =
    F.original.expansion cs μ (Finsupp.single (F.paired (b, r)) d) ≫
      sameColourTargetCross (Sc := Sc) μ P Q i := by
  rw [F.original_cross]
  exact F.residual.targetPositiveColumn_in_choice cs μ i F.swapped F.swappedPaired
    F.swapped_row N b r d hN hpos

/-- Actual nonpositive-height principal column, including the shifted block. -/
theorem nonpositive_column (N b : ℕ) (r : F.residual.Labels) (d : SYM D k)
    (hN : -D.h i (wt D μ Q) = (N : ℤ)) :
    F.swapped.expansion cs μ
      (F.residual.pairedRowsInclusion i F.swapped F.swappedPaired
        (MatchingTransition.rightColumn (k := k)
          (F.residual.targetNonpositiveColumn cs μ i N b r) d)) =
    F.original.expansion cs μ (Finsupp.single (F.paired (b, r)) d) ≫
      sameColourTargetCross (Sc := Sc) μ P Q i := by
  rw [F.original_cross]
  exact F.residual.targetNonpositiveColumn_in_choice cs μ i F.swapped F.swappedPaired
    F.swapped_row N b r d hN

end SameColourTargetFrame
end OddMath.SKM
