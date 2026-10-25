import OddMath.SKM.SourceCapState

/-! Contextual cap attachment with two colours and nonempty contexts. -/
namespace OddMath.SKM.SourceCapStateExamples
open StringDiagrams StringDiagrams.Chord

private def L : List (Letter Bool) := [up true]
private def Q : List (Letter Bool) := [dn true]

theorem cap_representative :
    IsMatching₂ (L ++ dn false :: up false :: Q) (L ++ Q) [.cap L.length] ∧
    StrictReduced₂ (L ++ dn false :: up false :: Q) [.cap L.length] :=
  ⟨SourceCapState.cap_matching L Q (up false), SourceCapState.cap_strict L Q (up false)⟩

theorem surviving_id :
    idAt (SourceCapState.capped L Q (up false)).st 1 = some 4 ∧
    idAt (SourceCapState.capped L Q (up false)).st 2 = some 4 :=
  SourceCapState.frozen_cap_ids L Q (up false)

theorem cap_then_suffix (R : List (TMove (Letter Bool))) :
    tLay (L ++ dn false :: up false :: Q) (.cap L.length :: R) =
      (xCapL (up false)).map (xwhL L Q) ++ tLay (L ++ Q) R :=
  SourceCapState.cap_layers L Q (up false) R

#print axioms cap_representative
#print axioms surviving_id
#print axioms cap_then_suffix
end OddMath.SKM.SourceCapStateExamples
