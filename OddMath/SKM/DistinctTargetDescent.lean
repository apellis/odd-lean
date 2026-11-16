import OddMath.SKM.DistinctExchangeIndependence
import OddMath.SKM.AdaptedDistinctChoices
import OddMath.SKM.ContextualNondegeneracy
import OddMath.SKM.MatchingChoiceCast

/-! The distinct-colour target branch of contextual sorting, using actual
complete adapted families and their literal terminal crossings. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc)

/-- Distinct colours require only independence of the swapped boundary.
The adapted choices, labels, serializers, and crossing comparison are all
constructed internally; coefficients are arbitrary elements of full SYM. -/
theorem distinct_target_exchange_descent (μ : X) (a L Q : List (Letter I))
    (i j : I) (hij : i ≠ j)
    (h : BoundaryIndependence cs μ a (L ++ dn j :: up i :: Q)) :
    BoundaryIndependence cs μ a (L ++ up i :: dn j :: Q) := by
  intro hab F
  obtain ⟨A, B, e, he⟩ := exists_adapted_distinct_colour_choices a L Q (up i) (dn j) hij
  have hw : wt D 0 a = wt D 0 (L ++ dn j :: up i :: Q) :=
    hab.trans (wt_context_opposite_swap 0 L Q j i).symm
  have hB := h hw B
  have eA : L ++ [up i, dn j] ++ Q = L ++ up i :: dn j :: Q := by simp
  have eB : L ++ [dn j, up i] ++ Q = L ++ dn j :: up i :: Q := by simp
  let A' := A.cast rfl eA.symm
  let B' := B.cast rfl eB.symm
  let ea := A.castLabelsEquiv rfl eA.symm
  let eb := B.castLabelsEquiv rfl eB.symm
  let e' := ea.symm.trans (e.trans eb)
  have hB' : Function.Injective (B'.expansion cs μ) :=
    (B.cast_expansion_injective_iff cs μ rfl eB.symm).mpr hB
  have hA' : Function.Injective (A'.expansion cs μ) := by
    apply distinct_target_adapted_independent cs μ a L Q j i hij.symm A' B' e' ?_ hB'
    intro t
    obtain ⟨s, rfl⟩ := ea.surjective t
    have he' : e' (ea s) = eb (e s) := by simp [e']
    rw [he']
    have ha : A'.layers (ea s) = A.layers s := A.cast_layers rfl eA.symm s
    have hb : B'.layers (eb (e s)) = B.layers (e s) := B.cast_layers rfl eB.symm (e s)
    rcases he s with hlo | hhi
    · have H : B'.layers (eb (e s)) = A'.layers (ea s) ++
          (xCrL (up i) (dn j)).map (xwhL L Q) := by rw [ha, hb, hlo]
      rw [H]
      exact distinct_target_low_eval cs μ j i (A'.layers_chain (ea s))
    · have H : A'.layers (ea s) = B'.layers (eb (e s)) ++
          (xCrL (dn j) (up i)).map (xwhL L Q) := by rw [ha, hb, hhi]
      rw [H]
      exact distinct_target_high_eval cs μ j i hij.symm (B'.layers_chain (eb (e s)))
  have hA := (A.cast_expansion_injective_iff cs μ rfl eA.symm).mp hA'
  exact F.expansion_injective_of_choice cs μ A hA

end OddMath.SKM
