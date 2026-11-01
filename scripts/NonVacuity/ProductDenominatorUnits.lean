import OddMath.QuiverHecke.SwappedAssembly.ProductDenominatorUnits
import Mathlib.Algebra.Category.ModuleCat.Basic
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory
open OddMath.QuiverHecke.SwappedAssembly
namespace OddMath.QuiverHecke.ProductDenominatorUnitsExamples

private abbrev V := ModuleCat.of ℚ (ℚ × ℚ)
private def upper (a : ℚ) : End V :=
  ModuleCat.ofHom {
    toFun := fun v => (a * v.2, 0)
    map_add' := by intros; ext <;> simp [mul_add]
    map_smul' := by intros; ext <;> simp [mul_comm, mul_left_comm, mul_assoc] }

private def diagonal : End V :=
  ModuleCat.ofHom {
    toFun := fun v => (v.1, -v.2)
    map_add' := by intros; ext <;> simp
    map_smul' := by intros; ext <;> simp }

private theorem upper_nilpotent (a : ℚ) : IsNilpotent (upper a) := by
  refine ⟨2, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  apply Prod.ext <;> simp [upper, pow_two, End.mul_def]

private theorem diagonal_square : diagonal * diagonal = 1 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  apply Prod.ext <;> simp [diagonal, End.mul_def]

private theorem diagonal_unit : IsUnit diagonal :=
  ⟨⟨diagonal, diagonal, diagonal_square, diagonal_square⟩, rfl⟩

private theorem upper_diagonal (a : ℚ) :
    upper a * diagonal = -(diagonal * upper a) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  apply Prod.ext <;> simp [upper, diagonal, End.mul_def]

private abbrev Categories : ℕ → Type 1 := fun _ => ModuleCat ℚ
private abbrev Objects : ∀ n : ℕ, Categories n := fun _ => V
private def nilDots : End Objects := fun n => upper (n + 1)
private def oddDots : End Objects := fun _ => diagonal

example : IsUnit (nilDots - 1) := by
  apply product_difference_isUnit Categories Objects
  · intro n; exact isUnit_one
  · intro n; exact upper_nilpotent _
  · intro n; simp [Commute, SemiconjBy]

example : IsUnit (oddDots ^ 2 - nilDots ^ 2) := by
  apply product_square_difference_isUnit Categories Objects
  · intro n; exact diagonal_unit
  · intro n; exact upper_nilpotent _
  · intro n; exact upper_diagonal _

example : IsUnit (oddDots ^ 2 + nilDots ^ 2) := by
  apply product_square_sum_isUnit Categories Objects
  · intro n; exact diagonal_unit
  · intro n; exact upper_nilpotent _
  · intro n; exact upper_diagonal _

end OddMath.QuiverHecke.ProductDenominatorUnitsExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.ProductDenominatorUnits
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
