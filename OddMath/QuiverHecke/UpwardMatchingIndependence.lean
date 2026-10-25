/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CanonicalPBWChoiceComparison
import OddMath.SKM.WeakMateIndependence
import OddMath.SKM.CanonicalUpwardMatching

/-! # From actual upward coefficient detection to matching independence -/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams StringDiagrams.Chord
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

theorem matching_upward_length_eq {t t' : List I} {R : List (TMove (SKM.Letter I))}
    (hR : SKM.IsMatching₂ (upWord t) (upWord t') R) : t.length = t'.length := by
  have hs : (List.ofFn fun r : Fin t.length => (true, t.get r)) = upWord t := by
    simpa only [List.map_ofFn, Function.comp_def, upWord, SKM.up] using
      congrArg (List.map (fun i : I => (true, i))) (List.ofFn_get t)
  have ht : (List.ofFn fun r : Fin t'.length => (true, t'.get r)) = upWord t' := by
    simpa only [List.map_ofFn, Function.comp_def, upWord, SKM.up] using
      congrArg (List.map (fun i : I => (true, i))) (List.ofFn_get t')
  have hm : SKM.IsMatching₂ (List.ofFn fun r : Fin t.length => (true, t.get r))
      (List.ofFn fun r : Fin t'.length => (true, t'.get r)) R := by
    simpa only [hs, ht] using hR
  exact hm.positive_length_eq t.get t'.get

theorem upward_choice_injective_of_length_ne {t t' : List I}
    (h : t.length ≠ t'.length) (μ : X) (F : SKM.MatchingBasisChoice (upWord t) (upWord t')) :
    Function.Injective (F.expansion cs μ) := by
  intro f g _
  ext z
  exact False.elim (h (matching_upward_length_eq (F.matching z.1.val z.1.property).1))

/-- The native canonical crossing matching choice identifies affine PBW
independence with the full matching-choice upward hypothesis used by sorting.
There is no additional matching-basis or serializer premise. -/
theorem upward_independence_of_coefficientMap
    (hUp : ∀ (a b : List I), SKM.wt D 0 (SKM.ups a) = SKM.wt D 0 (SKM.ups b) →
      ∀ μ : X, Function.Injective (upwardCoefficientMap D Sc cs μ a b)) :
    SKM.WeakMate.UpwardIndependence cs := by
  intro a b hw μ U
  by_cases hlen : a.length = b.length
  · let F := SKM.CanonicalUpward.choiceList a b hlen
    have hF : Function.Injective (F.expansion cs μ) :=
      canonicalChoice_independence D Sc cs F
        (SKM.CanonicalUpward.choiceList_word a b hlen)
        (SKM.CanonicalUpward.choiceList_word_spec a b hlen) μ (hUp a b hw μ)
    exact U.expansion_injective_of_choice cs μ F hF
  · exact upward_choice_injective_of_length_ne D Sc cs hlen μ U

/-- The exact action obligation at each fixed external weight implies full
upward independence for every complete matching choice. -/
theorem upward_independence_of_finite_observations
    (hobs : ∀ (a b : List I), SKM.wt D 0 (SKM.ups a) = SKM.wt D 0 (SKM.ups b) →
      ∀ μ : X, FiniteUpwardObservations D Sc cs μ a b) :
    SKM.WeakMate.UpwardIndependence cs := by
  apply upward_independence_of_coefficientMap D Sc cs
  intro a b hw μ
  exact upwardCoefficientMap_injective_of_observations D Sc cs μ a b (hobs a b hw μ)

end OddMath.QuiverHecke
