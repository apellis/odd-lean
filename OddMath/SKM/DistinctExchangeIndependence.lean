import OddMath.SKM.DistinctContextualCrossing
import OddMath.SKM.MatchingCoefficientPlacement
import OddMath.SKM.MatchingChoiceTransition

/-! Independence transfer for actual adapted distinct-color matching families.
The family construction and serializer correspondence are separate diagrammatic
inputs; the crossing action and full coefficient comparison here are native. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc)

theorem xev_contextualSigma (μ : X) (L Q : List (Letter I)) (i j : I) :
    xev cs μ (L ++ [up j, dn i] ++ Q) (L ++ [dn i, up j] ++ Q)
      ((xCrL (up j) (dn i)).map (xwhL L Q)) = contextualSigma μ L Q i j := by
  change xev cs μ _ _ (((sigmaL i j).map ofL).map (xwhL L Q)) = _
  rw [map_xwhL_map_ofL, xev_map_ofL]
  rfl

theorem xev_contextualLCross (μ : X) (L Q : List (Letter I)) (i j : I) :
    xev cs μ (L ++ [dn i, up j] ++ Q) (L ++ [up j, dn i] ++ Q)
      ((xCrL (dn i) (up j)).map (xwhL L Q)) = contextualLCross μ L Q i j := by
  change xev cs μ _ _ (((lcrossL i j).map ofL).map (xwhL L Q)) = _
  rw [map_xwhL_map_ofL, xev_map_ofL]
  rfl

/-- On the low-crossing side the actual terminal crossing is the chosen
partner, including every decoration already present in the common prefix. -/
theorem distinct_target_low_eval (μ : X) {a L Q : List (Letter I)} (i j : I)
    {P : List (XLayer I)} (hP : XChain a P (L ++ [up j, dn i] ++ Q)) :
    xev cs μ a (L ++ [up j, dn i] ++ Q) P ≫ contextualSigma μ L Q i j =
      xev cs μ a (L ++ [dn i, up j] ++ Q) (P ++ (xCrL (up j) (dn i)).map (xwhL L Q)) := by
  rw [xev_append cs _ hP, xev_contextualSigma]

/-- On the high-crossing side the actual inverse terminal crossing cancels
exactly, with coefficient +1 and no residual diagrams. -/
theorem distinct_target_high_eval (μ : X) {a L Q : List (Letter I)} (i j : I) (hij : i ≠ j)
    {P : List (XLayer I)} (hP : XChain a P (L ++ [dn i, up j] ++ Q)) :
    xev cs μ a (L ++ [up j, dn i] ++ Q)
      (P ++ (xCrL (dn i) (up j)).map (xwhL L Q)) ≫ contextualSigma μ L Q i j =
        xev cs μ a (L ++ [dn i, up j] ++ Q) P := by
  rw [xev_append cs _ hP, xev_contextualLCross, Category.assoc,
    contextualLCross_sigma μ L Q i j hij, Category.comp_id]

/-- Source low-side insertion, for arbitrary subsequent decorated layers. -/
theorem distinct_source_low_eval (μ : X) (L Q b : List (Letter I)) (i j : I)
    (P : List (XLayer I)) :
    contextualSigma μ L Q i j ≫ xev cs μ (L ++ [dn i, up j] ++ Q) b P =
      xev cs μ (L ++ [up j, dn i] ++ Q) b ((xCrL (up j) (dn i)).map (xwhL L Q) ++ P) := by
  rw [xev_append cs _ ((xChain_xCrL (up j) (dn i)).whisk L Q), xev_contextualSigma]

/-- Source high-side cancellation with no correction term or scalar factor. -/
theorem distinct_source_high_eval (μ : X) (L Q b : List (Letter I)) (i j : I) (hij : i ≠ j)
    (P : List (XLayer I)) :
    contextualSigma μ L Q i j ≫ xev cs μ (L ++ [dn i, up j] ++ Q) b
      ((xCrL (dn i) (up j)).map (xwhL L Q) ++ P) =
        xev cs μ (L ++ [up j, dn i] ++ Q) b P := by
  rw [xev_append cs _ ((xChain_xCrL (dn i) (up j)).whisk L Q), xev_contextualLCross,
    ← Category.assoc, contextualSigma_lcross μ L Q i j hij, Category.id_comp]

/-- An actual terminal-crossing correspondence transfers independence on
full source-placed coefficients, with no parity or t_ij correction. -/
theorem distinct_target_adapted_independent (μ : X) (a L Q : List (Letter I))
    (i j : I) (hij : i ≠ j)
    (F : MatchingBasisChoice a (L ++ [up j, dn i] ++ Q))
    (G : MatchingBasisChoice a (L ++ [dn i, up j] ++ Q))
    (e : F.Labels ≃ G.Labels)
    (he : ∀ t, xev cs μ a (L ++ [up j, dn i] ++ Q) (F.layers t) ≫
      contextualSigma μ L Q i j = xev cs μ a (L ++ [dn i, up j] ++ Q) (G.layers (e t)))
    (hG : Function.Injective (G.expansion cs μ)) : Function.Injective (F.expansion cs μ) := by
  let E : (F.Labels →₀ SYM D k) ≃ₗ[k] (G.Labels →₀ SYM D k) := Finsupp.domLCongr e
  have H : ∀ v, distinctTargetExchange μ a L Q i j hij (F.expansion cs μ v) = G.expansion cs μ (E v) := by
    intro v
    classical
    induction v using Finsupp.induction with
    | zero => simp only [map_zero]
    | @single_add t p v _ _ ih =>
      rw [map_add, map_add, map_add, map_add, ih]
      congr 1
      rw [F.expansion_single, distinctTargetExchange_coefficient]
      have hs : E (Finsupp.single t p) = Finsupp.single (e t) p := by simp [E]
      rw [hs, G.expansion_single]
      change _ ≫ (_ ≫ contextualSigma μ L Q i j) = _
      rw [he]
  intro v w hvw
  apply E.injective
  apply hG
  rw [← H, ← H, hvw]

/-- The source-side correspondence is untwisted in target placement; the
proved parity involution converts the resulting independence back to the
library's source convention, retaining every full-SYM coefficient. -/
theorem distinct_source_adapted_independent (μ : X) (L Q b : List (Letter I))
    (i j : I) (hij : i ≠ j)
    (F : MatchingBasisChoice (L ++ [dn i, up j] ++ Q) b)
    (G : MatchingBasisChoice (L ++ [up j, dn i] ++ Q) b)
    (e : F.Labels ≃ G.Labels)
    (he : ∀ t, contextualSigma μ L Q i j ≫
      xev cs μ (L ++ [dn i, up j] ++ Q) b (F.layers t) =
        xev cs μ (L ++ [up j, dn i] ++ Q) b (G.layers (e t)))
    (hG : Function.Injective (G.expansion cs μ)) : Function.Injective (F.expansion cs μ) := by
  apply (F.expansion_injective_iff_target cs μ).mpr
  have hGt := (G.expansion_injective_iff_target cs μ).mp hG
  let E : (F.Labels →₀ SYM D k) ≃ₗ[k] (G.Labels →₀ SYM D k) := Finsupp.domLCongr e
  have H : ∀ v, distinctSourceExchange μ L Q b i j hij (F.targetExpansion cs μ v) =
      G.targetExpansion cs μ (E v) := by
    intro v
    classical
    induction v using Finsupp.induction with
    | zero => simp only [map_zero]
    | @single_add t p v _ _ ih =>
      rw [map_add, map_add, map_add, map_add, ih]
      congr 1
      have hs : E (Finsupp.single t p) = Finsupp.single (e t) p := by simp [E]
      rw [hs, F.targetExpansion_single, G.targetExpansion_single]
      change contextualSigma μ L Q i j ≫ (_ ≫ _) = _
      rw [← Category.assoc, he]
  intro v w hvw
  apply E.injective
  apply hGt
  rw [← H, ← H, hvw]

end OddMath.SKM
