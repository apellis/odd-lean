import OddMath.QuiverHecke.SwappedAssembly.ReservoirPaths
import Lean.Util.CollectAxioms

noncomputable section
open OddMath.SKM OddMath.QuiverHecke.SwappedAssembly
namespace OddMath.QuiverHecke.SwappedReservoirPathExamples

private def word : List (Col Bool ℤ) :=
  [⟨(true, false), 0⟩, ⟨(true, true), 17⟩, ⟨(true, false), -3⟩]
private theorem upward : ∀ c ∈ word, c.l.1 = true := by simp [word]
private def terminal : Bool →₀ ℕ := Finsupp.single true 2

/-- Two colours, a repeated colour, independent labels, and positive terminal content. -/
example : Nonempty (SPath word (0, SPath.wordContent word + terminal) (0, terminal)) :=
  ⟨SPath.reservoirPath word upward terminal⟩

example : SPath.wordContent word + terminal =
    Finsupp.single false 2 + Finsupp.single true 3 := by
  ext i
  cases i <;> simp [SPath.wordContent, word, terminal]

/-- A canonical occupied vacuum path retains a nonzero coefficient sum. -/
example :
    letI := Fintype.ofFinite (SPath word (0, SPath.wordContent word + 0) (0, 0))
    ∑ _q : SPath word (0, SPath.wordContent word + 0) (0, 0), (7 : ℚ) = 7 := by
  let := Fintype.ofFinite (SPath word (0, SPath.wordContent word + 0) (0, 0))
  exact SPath.sum_of_upward_probe_zero upward rfl (fun _ => 7)
    (SPath.reservoirPath word upward 0)

end OddMath.QuiverHecke.SwappedReservoirPathExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.ReservoirPaths
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
