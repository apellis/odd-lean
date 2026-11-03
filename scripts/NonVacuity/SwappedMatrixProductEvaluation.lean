import OddMath.QuiverHecke.SwappedAssembly.Supernatural.MatrixProductEvaluation
import Mathlib.Algebra.Category.ModuleCat.Basic
import Lean.Util.CollectAxioms
noncomputable section
open scoped Classical
open CategoryTheory
open OddMath.QuiverHecke.SwappedAssembly
namespace MatrixProductEvaluationConsumer
private def V : Mat_ (ModuleCat ℚ) := ⟨Bool, fun _ => ModuleCat.of ℚ ℚ⟩
private def a (n : ℕ) : V ⟶ V := fun i j =>
  if i = j then 𝟙 _ else if i = false then (n + 1 : ℚ) • 𝟙 _ else 0
private def b (n : ℕ) : V ⟶ V := fun i j =>
  if i = j then 𝟙 _ else if i = false then -((n + 1 : ℚ) • 𝟙 _) else 0
private theorem ab (n : ℕ) : a n ≫ b n = 𝟙 V := by
  apply Mat_.hom_ext
  intro i j
  cases i <;> cases j <;>
    simp [Mat_.comp_apply, a, b, V]
private theorem ba (n : ℕ) : b n ≫ a n = 𝟙 V := by
  apply Mat_.hom_ext
  intro i j
  cases i <;> cases j <;>
    simp [Mat_.comp_apply, a, b, V]
private def F : Mat_ (ℕ → ModuleCat ℚ) := ⟨Bool, fun _ _ => ModuleCat.of ℚ ℚ⟩
private def f : F ⟶ F := fun i j n => a n i j
private theorem at_iso (n : ℕ) :
    IsIso ((MatrixProductEvaluation.evaluation (fun _ : ℕ => ModuleCat ℚ) n).map f) := by
  change IsIso (a n)
  exact ⟨b n, ab n, ba n⟩
example : IsIso f := MatrixProductEvaluation.isIso_of_components _ f at_iso
private theorem offdiag_apply (n : ℕ) : (f false true n) (1 : ℚ) = (n + 1 : ℚ) := by
  simp [f, a, V]
  change (n + 1 : ℚ) * 1 = n + 1
  exact mul_one _
example (n : ℕ) : f false true n ≠ 0 := by
  intro hz
  have h := congrArg (fun z => z (1 : ℚ)) hz
  change (f false true n) (1 : ℚ) = 0 at h
  rw [offdiag_apply] at h
  have hn : (n + 1 : ℚ) ≠ 0 := by positivity
  exact hn h
example {g h : F ⟶ F}
    (e : ∀ n, (MatrixProductEvaluation.evaluation (fun _ : ℕ => ModuleCat ℚ) n).map g =
      (MatrixProductEvaluation.evaluation (fun _ : ℕ => ModuleCat ℚ) n).map h) : g = h :=
  MatrixProductEvaluation.map_ext _ e
end MatrixProductEvaluationConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Supernatural.MatrixProductEvaluation
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
