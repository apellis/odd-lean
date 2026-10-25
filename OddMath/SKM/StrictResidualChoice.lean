import OddMath.SKM.IndexedMatchingChoice
import OddMath.SKM.MatchingChoiceTransition

/-! The residual serializers used in cup-completed matching families form a
complete choice in their own right. Their labels agree with the original
choice, but their layers need not agree with its chosen serializers. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
universe u v w
variable {I : Type u} {a b : List (Letter I)}
namespace MatchingBasisChoice

/-- Repoint each strict representative using the canonical strict serializer. -/
def strictResidual (B : MatchingBasisChoice a b) (j : B.members) : PointedMatching a b :=
  PointedMatching.ofStrict (B.matching j j.property).1 (B.matching j j.property).2

theorem strictResidual_unique (B : MatchingBasisChoice a b) (j l : B.members)
    (h : Iso (pairing₂ a (B.strictResidual j).moves) (pairing₂ a (B.strictResidual l).moves)) :
    j = l := by
  apply Subtype.ext
  exact B.unique _ j.property _ l.property h

theorem strictResidual_complete (B : MatchingBasisChoice a b)
    (R : List (TMove (Letter I))) (hR : IsMatching₂ a b R) (hr : StrictReduced₂ a R) :
    ∃ j, Iso (pairing₂ a (B.strictResidual j).moves) (pairing₂ a R) := by
  obtain ⟨S, hS, hi⟩ := B.complete R hR hr
  exact ⟨⟨S, hS⟩, hi⟩

/-- Complete residual choice with exactly the strict serializers used by cup completion. -/
def strictResidualChoice (B : MatchingBasisChoice a b) : MatchingBasisChoice a b :=
  IndexedMatchingChoice.choice B.strictResidual B.strictResidual_unique B.strictResidual_complete

def strictResidualLabels (B : MatchingBasisChoice a b) : B.Labels ≃ B.strictResidualChoice.Labels :=
  IndexedMatchingChoice.labelsEquiv B.strictResidual B.strictResidual_unique B.strictResidual_complete

@[simp] theorem strictResidualChoice_layers (B : MatchingBasisChoice a b)
    (j : B.members) (n : MatchingStrand a j.val → ℕ) :
    B.strictResidualChoice.layers (B.strictResidualLabels ⟨j, n⟩) =
      (B.strictResidual j).layers n :=
  IndexedMatchingChoice.layers_labelsEquiv B.strictResidual B.strictResidual_unique
    B.strictResidual_complete j n

variable {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- Residual independence transfers by choice invariance, not by an unsupported
identification of serializers. This retains the full abstract SYM coefficients. -/
theorem strictResidualChoice_independent (B : MatchingBasisChoice a b)
    (cs : CScalars Sc) (μ : X) (hB : Function.Injective (B.expansion cs μ)) :
    Function.Injective (B.strictResidualChoice.expansion cs μ) :=
  B.strictResidualChoice.expansion_injective_of_choice cs μ B hB

end MatchingBasisChoice
end OddMath.SKM
