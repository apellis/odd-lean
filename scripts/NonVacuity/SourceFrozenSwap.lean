import OddMath.SKM.SourceFrozenSwap

namespace NonVacuity.SourceFrozenSwap
open StringDiagrams StringDiagrams.Chord OddMath.SKM.SourceFrozenSwap

private def T : TState Bool := ⟨2, [(0, true), (1, false), (0, false), (1, true)], []⟩
private def R : List (TMove Bool) := [.cap 0, .mv (.cup 0 true), .mv (.cross 0)]

private theorem valid : TFits Bool.not 2 T R := by
  refine ⟨⟨(0, false), (1, true), rfl, rfl, rfl, by decide⟩, ?_, ?_, trivial⟩ <;>
    (simp only [TMove.Ok]; decide)

/-- The cap actually renames a frozen endpoint ID; validity still transports
through the following cup and crossing. -/
example : TFits Bool.not 2 (frozen 0 T) R := fits Bool.not (by decide) T R valid

example : tRun Bool.not 2 (frozen 0 T) R = frozen 0 (tRun Bool.not 2 T R) :=
  run Bool.not (by decide) T R valid

#print axioms OddMath.SKM.SourceFrozenSwap.run
end NonVacuity.SourceFrozenSwap
