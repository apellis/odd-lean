import OddMath.SKM.AdaptedSameColourChoices
import OddMath.SKM.StrictResidualChoice
import OddMath.SKM.PairedCupEvaluation

/-! Complete same-colour families with their evaluated paired rows. The
residual choice is rebuilt with its strict serializers before it is used;
thus the residual expansion is the one occurring in the literal cup rows. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams StringDiagrams.Chord Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- The complete adapted choices have the native paired rows at every dot
count and external weight, with one common complete residual choice. -/
theorem exists_same_colour_cup_rows (cs : CScalars Sc) (μ : X)
    (a P Q : List (Letter I)) (i : I) :
    ∃ (B : MatchingBasisChoice a (P ++ Q))
      (F : MatchingBasisChoice a (P ++ up i :: dn i :: Q))
      (G : MatchingBasisChoice a (P ++ dn i :: up i :: Q))
      (e : F.Labels ≃ G.Labels) (p : ℕ × B.Labels ↪ F.Labels),
      (∀ t, t ∉ Set.range p →
        G.layers (e t) = F.layers t ++ (xCrL (up i) (dn i)).map (xwhL P Q) ∨
        F.layers t = G.layers (e t) ++ (xCrL (dn i) (up i)).map (xwhL P Q)) ∧
      (∀ b r,
        xev cs μ a (P ++ up i :: dn i :: Q) (F.layers (p (b, r))) =
          xev cs μ a (P ++ Q) (B.layers r) ≫
            plcW μ (P ++ Q) (P ++ up i :: dn i :: Q) P Q [] [up i, dn i]
              (etaP cs i (wt D μ Q) ≫ cpow (uLM D Sc i (wt D μ Q)) b)) ∧
      (∀ b r,
        xev cs μ a (P ++ dn i :: up i :: Q) (G.layers (e (p (b, r)))) =
          xev cs μ a (P ++ Q) (B.layers r) ≫
            plcW μ (P ++ Q) (P ++ dn i :: up i :: Q) P Q [] [dn i, up i]
              (hLM D Sc i (wt D μ Q) b)) := by
  obtain ⟨B, F, G, e, p, hu, hp⟩ := exists_same_colour_adapted_equiv a P Q true i
  let E : ℕ × B.strictResidualChoice.Labels ≃ ℕ × B.Labels :=
    Equiv.prodCongr (Equiv.refl ℕ) B.strictResidualLabels.symm
  let p' : ℕ × B.strictResidualChoice.Labels ↪ F.Labels := E.toEmbedding.trans p
  refine ⟨B.strictResidualChoice, F, G, e, p', ?_, ?_, ?_⟩
  · intro t ht
    apply hu t
    rintro ⟨z, rfl⟩
    apply ht
    exact ⟨E.symm z, congrArg p (E.apply_symm_apply z)⟩
  · intro b r
    obtain ⟨⟨j, n⟩, rfl⟩ := B.strictResidualLabels.surjective r
    have H := (hp b j n).1
    have hl := (B.strictResidual j).appendCup_layers true i b n
    have he := (B.strictResidual j).appendCup_up_eval cs μ i b n
    rw [B.strictResidualChoice_layers]
    have hp' : p' (b, B.strictResidualLabels ⟨j, n⟩) = p (b, ⟨j, n⟩) := by
      simp [p', E]
    rw [hl] at he
    rw [hp', H]
    exact he
  · intro b r
    obtain ⟨⟨j, n⟩, rfl⟩ := B.strictResidualLabels.surjective r
    have H := (hp b j n).2
    have hl := (B.strictResidual j).appendCup_layers false i b n
    have he := (B.strictResidual j).appendCup_dn_eval cs μ i b n
    rw [B.strictResidualChoice_layers]
    have hp' : p' (b, B.strictResidualLabels ⟨j, n⟩) = p (b, ⟨j, n⟩) := by
      simp [p', E]
    rw [hl] at he
    rw [hp', H]
    exact he

end OddMath.SKM
