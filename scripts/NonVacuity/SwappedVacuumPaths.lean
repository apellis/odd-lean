import OddMath.QuiverHecke.SwappedAssembly.VacuumPaths
import Lean.Util.CollectAxioms

noncomputable section
open OddMath.SKM OddMath.QuiverHecke.SwappedAssembly
namespace OddMath.QuiverHecke.SwappedVacuumPathExamples

private def colour : Col Unit Unit := ⟨(true, ()), ()⟩
private def sector (n : ℕ) : Sector Unit := (0, Finsupp.single () n)

private def prepend {w : List (Col Unit Unit)} (n : ℕ)
    (p : SPath w (sector n) (sector 0)) :
    SPath (colour :: w) (sector (n + 1)) (sector 0) := by
  have hs : nextSector (true, ()) false (sector (n + 1)) = sector n := by
    simp [nextSector, sector]
  exact .cons colour false (sector (n + 1))
    (by simp [colour, StepValid, sector]) (hs.symm ▸ p)

/-- An occupied length-three path with repeated colour and positive reservoir content. -/
private def triple : SPath [colour, colour, colour] (sector 3) (sector 0) :=
  prepend 2 (prepend 1 (prepend 0 (.nil (sector 0))))

example : Nonempty (SPath [colour, colour, colour] (sector 3) (sector 0)) := ⟨triple⟩

example : Subsingleton (SPath [colour, colour, colour] (sector 3) (sector 0)) :=
  SPath.subsingleton_of_upward_probe_zero (by simp [colour]) rfl

/-- A nonzero summand survives the entire finite path sum. -/
example :
    letI := Fintype.ofFinite (SPath [colour, colour, colour] (sector 3) (sector 0))
    ∑ _q : SPath [colour, colour, colour] (sector 3) (sector 0), (7 : ℕ) = 7 := by
  let := Fintype.ofFinite (SPath [colour, colour, colour] (sector 3) (sector 0))
  exact SPath.sum_of_upward_probe_zero (by simp [colour]) rfl (fun _ => 7) triple

end OddMath.QuiverHecke.SwappedVacuumPathExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.VacuumPaths
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
