import OddMath.SKM.SourceAdaptedChoices
import OddMath.SKM.StrictResidualChoice
import OddMath.SKM.ResidualCoefficientLift

/-! Complete source exchange frames with exactly the serializers supplied by
source completion. The cap dots are on the left selected endpoint. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u}

/-- A complete source frame, with a common strict residual serializer. -/
structure SameColourSourceFrame (P Q Z : List (Letter I)) (i : I) where
  residual : MatchingBasisChoice (P ++ Q) Z
  original : MatchingBasisChoice (P ++ dn i :: up i :: Q) Z
  swapped : MatchingBasisChoice (P ++ up i :: dn i :: Q) Z
  exchange : original.Labels ≃ swapped.Labels
  paired : ℕ × residual.Labels ↪ original.Labels
  unpaired : ∀ t, t ∉ Set.range paired →
    swapped.layers (exchange t) = (xCrL (up i) (dn i)).map (xwhL P Q) ++ original.layers t ∨
    original.layers t = (xCrL (dn i) (up i)).map (xwhL P Q) ++ swapped.layers (exchange t)
  original_layers : ∀ b r, original.layers (paired (b, r)) =
    (List.replicate b (dotOn (P ++ dn i :: up i :: Q) P.length)).flatten ++
      (xCapL (up i)).map (xwhL P Q) ++ residual.layers r
  swapped_layers : ∀ b r, swapped.layers (exchange (paired (b, r))) =
    (List.replicate b (dotOn (P ++ up i :: dn i :: Q) P.length)).flatten ++
      (xCapL (dn i)).map (xwhL P Q) ++ residual.layers r

/-- Completeness is unconditional and does not use any independence theorem. -/
theorem sameColourSourceFrame_nonempty (P Q Z : List (Letter I)) (i : I) :
    Nonempty (SameColourSourceFrame P Q Z i) := by
  obtain ⟨B, F, G, e, p, hu, hp⟩ := exists_source_same_colour_adapted_equiv Z P Q true i
  let E : ℕ × B.strictResidualChoice.Labels ≃ ℕ × B.Labels :=
    Equiv.prodCongr (Equiv.refl ℕ) B.strictResidualLabels.symm
  let p' : ℕ × B.strictResidualChoice.Labels ↪ F.Labels := E.toEmbedding.trans p
  refine ⟨⟨B.strictResidualChoice, F, G, e, p', ?_, ?_, ?_⟩⟩
  · intro t ht
    apply hu t
    rintro ⟨z, rfl⟩
    exact ht ⟨E.symm z, congrArg p (E.apply_symm_apply z)⟩
  · intro b r
    obtain ⟨⟨j, n⟩, rfl⟩ := B.strictResidualLabels.surjective r
    have hp' : p' (b, B.strictResidualLabels ⟨j, n⟩) = p (b, ⟨j, n⟩) := by
      simp [p', E]
    change F.layers (p' (b, B.strictResidualLabels ⟨j, n⟩)) = _
    simp only [hp', B.strictResidualChoice_layers]
    exact (hp b j n).1
  · intro b r
    obtain ⟨⟨j, n⟩, rfl⟩ := B.strictResidualLabels.surjective r
    have hp' : p' (b, B.strictResidualLabels ⟨j, n⟩) = p (b, ⟨j, n⟩) := by
      simp [p', E]
    change G.layers (e (p' (b, B.strictResidualLabels ⟨j, n⟩))) = _
    simp only [hp', B.strictResidualChoice_layers]
    exact (hp b j n).2

namespace SameColourSourceFrame
variable {P Q Z : List (Letter I)} {i : I} (F : SameColourSourceFrame P Q Z i)
variable {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- Paired labels in the complete swapped family. -/
def swappedPaired : ℕ × F.residual.Labels ↪ F.swapped.Labels :=
  F.paired.trans F.exchange.toEmbedding

/-- Inclusion of the complete original paired sector. -/
def originalPairedInclusion : ((F.residual.Labels × ℕ) →₀ SYM D k) →ₗ[k]
    (F.original.Labels →₀ SYM D k) :=
  Finsupp.lmapDomain (SYM D k) k (fun r => F.paired (r.2, r.1))

/-- The same inclusion in the complete swapped family. -/
def swappedPairedInclusion : ((F.residual.Labels × ℕ) →₀ SYM D k) →ₗ[k]
    (F.swapped.Labels →₀ SYM D k) :=
  Finsupp.lmapDomain (SYM D k) k (fun r => F.swappedPaired (r.2, r.1))

theorem originalPairedInclusion_injective :
    Function.Injective (F.originalPairedInclusion (D := D) (k := k)) := by
  apply Finsupp.mapDomain_injective
  intro r s he
  have H := F.paired.injective he
  exact Prod.ext (congrArg Prod.snd H) (congrArg Prod.fst H)

theorem swappedPairedInclusion_injective :
    Function.Injective (F.swappedPairedInclusion (D := D) (k := k)) := by
  apply Finsupp.mapDomain_injective
  intro r s he
  have H := F.swappedPaired.injective he
  exact Prod.ext (congrArg Prod.snd H) (congrArg Prod.fst H)

end SameColourSourceFrame
#print axioms sameColourSourceFrame_nonempty
end OddMath.SKM
