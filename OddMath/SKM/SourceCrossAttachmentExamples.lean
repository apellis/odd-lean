import OddMath.SKM.SourceCrossAttachment

/-! A nonempty two-colour initial-crossing consumer, including ID zero. -/
namespace OddMath.SKM.SourceCrossAttachmentExamples
open StringDiagrams StringDiagrams.Chord

/-- The empty right context moves ID zero; no fixed-zero premise is imposed. -/
theorem moves_zero : SourceCrossState.exchangeId 0 0 = 2 := by decide

/-- Actual pointed representatives and count equivalences for two distinct colours. -/
theorem adapted_pair :
    ∃ A : SourceCrossAttachment.AdaptedPointedPair [] [] [dn false, up true]
      (dn false) (up true),
      Iso (pairing₂ [dn false, up true] A.left.moves)
        (pairing₂ [dn false, up true] []) := by
  apply SourceCrossAttachment.exists_adapted_pointed_pair [] [] _ _ _
    (show IsMatching₂ [dn false, up true] [dn false, up true] [] from ⟨trivial, rfl⟩)
  change ¬ (0 ≠ 1 ∧ (some 0 : Option ℕ) ≠ none ∧ (some 0 : Option ℕ) = some 2)
  decide

#print axioms adapted_pair
#print axioms SourceCrossState.cross_run
#print axioms SourceCrossAttachment.attach
#print axioms SourceCrossAttachment.exists_adapted_pointed_pair
end OddMath.SKM.SourceCrossAttachmentExamples
