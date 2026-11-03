import OddMath.QuiverHecke.SwappedAssembly.Sigma.CentralPaths
import OddMath.QuiverHecke.SwappedAssembly.Sigma.MatrixEmbedding
import Mathlib.Algebra.Category.ModuleCat.Basic
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory OddMath.SKM OddMath.QuiverHecke.SwappedAssembly
open scoped ZeroObject
namespace SwappedCentralPathsConsumer
private def occupied : Sector Bool :=
  (Finsupp.single false 2 + Finsupp.single true 1,
   Finsupp.single false 1 + Finsupp.single true 2)
private def empty : Sector Bool := (0, 0)
private def mixed : Sector Bool := (Finsupp.single true 1, Finsupp.single false 1)
example (i : Bool) := SPath.centralUpDnEquiv i (0 : ℤ) 1 occupied
example (i : Bool) := SPath.centralDnUpEquiv i (0 : ℤ) 1 occupied
example (i : Bool) := SPath.centralUpDnEquiv i (0 : ℤ) 1 empty
example (i : Bool) := SPath.centralDnUpEquiv i (0 : ℤ) 1 empty
example (i : Bool) := SPath.centralUpDnEquiv i (0 : ℤ) 1 mixed
example (i : Bool) := SPath.centralDnUpEquiv i (0 : ℤ) 1 mixed
example (i : Bool) : ¬StepValid (up i) false empty := by
  cases i <;> simp [StepValid, empty]
example (i : Bool) : ¬StepValid (dn i) true empty := by
  cases i <;> simp [StepValid, empty]
example (i : Bool) := SPath.centralUpDn i (0 : ℤ) 1 empty ⟨true, trivial⟩
example (i : Bool) := SPath.centralDnUp i (0 : ℤ) 1 empty ⟨false, trivial⟩
example := SPath.centralNilEquiv (X := ℤ) empty
private def M : Mat_ (ModuleCat ℚ) where
  ι := Bool
  X b := if b then ModuleCat.of ℚ ℚ else 0
private def N : Mat_ (ModuleCat ℚ) where
  ι := Unit
  X _ := ModuleCat.of ℚ ℚ
private def inclusion : N.ι ↪ M.ι := ⟨fun _ => true, by intro a b _; cases a; cases b; rfl⟩
private def E (j : N.ι) : M.X (inclusion j) ≅ N.X j := Iso.refl _
private theorem missing (b : M.ι) (h : ∀ j, inclusion j ≠ b) : Limits.IsZero (M.X b) := by
  cases b
  · exact Limits.isZero_zero _
  · exact False.elim (h () rfl)
private def padded : M ≅ N := matrixEmbeddingIso M N inclusion E missing
example : padded.hom ≫ padded.inv = 𝟙 M := padded.hom_inv_id
example : padded.inv ≫ padded.hom = 𝟙 N := padded.inv_hom_id
example : padded.hom true () = 𝟙 (ModuleCat.of ℚ ℚ) := by
  simp [padded, matrixEmbeddingIso_hom_apply, E, inclusion, famId, M, N]
example : padded.hom true () ≠ 0 := by
  intro h
  have h' : (𝟙 (ModuleCat.of ℚ ℚ) : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ) = 0 := by
    simpa [padded, matrixEmbeddingIso_hom_apply, E, inclusion, famId, M, N] using h
  have := congrArg (fun f : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ => f 1) h'
  norm_num at this
example (f : N ⟶ N) := matrixEmbeddingMap_square padded padded f
end SwappedCentralPathsConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.SwappedAssembly.Sigma.CentralPaths,
      `OddMath.QuiverHecke.SwappedAssembly.Sigma.MatrixEmbedding] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
