import OddMath.SKM.DistinctExchangeIndependence
import OddMath.SKM.SourceAdaptedDistinctChoices
import OddMath.SKM.ContextualNondegeneracy
import OddMath.SKM.MatchingChoiceCast

/-! Distinct-colour contextual source descent from actual complete choices. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc)

/-- Distinct colours require only the swapped boundary, with no residual
independence or coefficient homogeneity assumption. -/
theorem distinct_source_exchange_descent (μ : X) (L Q b : List (Letter I))
    (i j : I) (hij : i ≠ j)
    (h : BoundaryIndependence cs μ (L ++ up j :: dn i :: Q) b) :
    BoundaryIndependence cs μ (L ++ dn i :: up j :: Q) b := by
  intro hab F
  obtain ⟨A, B, e, he⟩ := exists_source_adapted_distinct_colour_choices b L Q (dn i) (up j) hij
  have hw : wt D 0 (L ++ up j :: dn i :: Q) = wt D 0 b :=
    (wt_context_opposite_swap 0 L Q i j).symm.trans hab
  have hB := h hw B
  have eA : L ++ [dn i, up j] ++ Q = L ++ dn i :: up j :: Q := by simp
  have eB : L ++ [up j, dn i] ++ Q = L ++ up j :: dn i :: Q := by simp
  let A' := A.cast eA.symm rfl
  let B' := B.cast eB.symm rfl
  let ea := A.castLabelsEquiv eA.symm rfl
  let eb := B.castLabelsEquiv eB.symm rfl
  let e' := ea.symm.trans (e.trans eb)
  have hB' : Function.Injective (B'.expansion cs μ) :=
    (B.cast_expansion_injective_iff cs μ eB.symm rfl).mpr hB
  have hA' : Function.Injective (A'.expansion cs μ) := by
    apply distinct_source_adapted_independent cs μ L Q b i j hij A' B' e' ?_ hB'
    intro t
    obtain ⟨s, rfl⟩ := ea.surjective t
    have he' : e' (ea s) = eb (e s) := by simp [e']
    rw [he']
    have ha : A'.layers (ea s) = A.layers s := A.cast_layers eA.symm rfl s
    have hb : B'.layers (eb (e s)) = B.layers (e s) := B.cast_layers eB.symm rfl (e s)
    rcases he s with hlo | hhi
    · have H : B'.layers (eb (e s)) =
          (xCrL (up j) (dn i)).map (xwhL L Q) ++ A'.layers (ea s) := by rw [ha, hb, hlo]
      rw [H]
      exact distinct_source_low_eval cs μ L Q b i j _
    · have H : A'.layers (ea s) =
          (xCrL (dn i) (up j)).map (xwhL L Q) ++ B'.layers (eb (e s)) := by rw [ha, hb, hhi]
      rw [H]
      exact distinct_source_high_eval cs μ L Q b i j hij _
  have hA := (A.cast_expansion_injective_iff cs μ eA.symm rfl).mp hA'
  exact F.expansion_injective_of_choice cs μ A hA

#print axioms distinct_source_exchange_descent
end OddMath.SKM
