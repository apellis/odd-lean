import OddMath.QuiverHecke.SwappedVacuum.NegativeCapMoments
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

/-! An occupied negative-height cap with N=2, P=1. The mate and unit
form a nontrivial invertible augmented matrix; no bubble value is assumed. -/
noncomputable section
namespace NonVacuity.SwappedNegativeCapMoments
open CategoryTheory OddMath.QuiverHecke.SwappedVacuum

private abbrev Line := ModuleCat.of ℚ ℚ
private abbrev Plane := ModuleCat.of ℚ (Fin 2 → ℚ)

private def reservoirDot : End Plane := ModuleCat.ofHom
  (LinearMap.pi fun j : Fin 2 => if j = 0 then LinearMap.proj 1 else 0)
private def unitColumn : Line ⟶ Plane := ModuleCat.ofHom
  (LinearMap.pi fun j : Fin 2 => if j = 0 then 0 else LinearMap.id)
private def mateColumn : Line ⟶ Plane := ModuleCat.ofHom
  (LinearMap.pi fun _ : Fin 2 => -LinearMap.id)
private def coefficientExtraction : Plane ⟶ Line := ModuleCat.ofHom (LinearMap.proj 0)
private def coefficients (n : ℕ) : ℚ := if n = 0 then -1 else if n = 1 then 1 else 0

private theorem slide : mateColumn ≫ reservoirDot - (1 : ℚ) • ((𝟙 Line) ≫ mateColumn) =
    (𝟙 Line) ≫ unitColumn := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext j
  fin_cases j <;> simp [mateColumn, reservoirDot, unitColumn]

private theorem window (a : ℕ) (ha : a < 2) :
    unitColumn ≫ (reservoirDot ^ a) ≫ coefficientExtraction =
      if a + 1 = 2 then 𝟙 Line else 0 := by
  interval_cases a <;> apply ModuleCat.hom_ext <;> apply LinearMap.ext <;> intro z <;>
    simp [unitColumn, reservoirDot, coefficientExtraction, End.one_def]

private theorem probe_relation : capPolynomial coefficients 1 (𝟙 Line) = 0 := by
  simp [capPolynomial, Finset.sum_range_succ, coefficients]

example : mateColumn ≫ capPolynomial coefficients 1 reservoirDot ≫ coefficientExtraction = 0 := by
  exact negative_cap_annihilates_mate (1 : ℚ) (𝟙 Line) reservoirDot mateColumn unitColumn
    (𝟙 Line) coefficientExtraction 2 1 (by norm_num) coefficients
    (by intro n hn; simp) slide window probe_relation

example : unitColumn ≫ capPolynomial coefficients 1 reservoirDot ≫ coefficientExtraction =
    𝟙 Line := by
  simpa [End.one_def] using
    negative_cap_unit_window reservoirDot unitColumn coefficientExtraction 2 1 coefficients
      (by simp [coefficients]) window 0 (by norm_num)

private def augmentedMap : Plane ⟶ Plane := ModuleCat.ofHom
  (LinearMap.pi fun j : Fin 2 => if j = 0 then
    -(LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 => ℚ) 0) else
    -(LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 => ℚ) 0) +
      LinearMap.proj (R := ℚ) (φ := fun _ : Fin 2 => ℚ) 1)

private def augmentedInverse : Plane ≅ Plane where
  hom := augmentedMap
  inv := augmentedMap
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext j
    fin_cases j <;> simp [augmentedMap]
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext j
    fin_cases j <;> simp [augmentedMap]

private def firstSourceColumn : Line ⟶ Plane := ModuleCat.ofHom
  (LinearMap.pi fun j : Fin 2 => if j = 0 then LinearMap.id (R := ℚ) else 0)

/-- The first source column of the whole matrix is the prescribed mate. -/
example : firstSourceColumn ≫ augmentedInverse.hom = mateColumn := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext j
  fin_cases j <;> simp [firstSourceColumn, augmentedInverse, augmentedMap, mateColumn]

/-- The second source column is the prescribed ordinary unit. -/
example : unitColumn ≫ augmentedInverse.hom = unitColumn := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext j
  fin_cases j <;> simp [unitColumn, augmentedInverse, augmentedMap]

/-- The polynomial candidate is the last row of the concrete whole inverse. -/
example : augmentedInverse.inv ≫ ModuleCat.ofHom (LinearMap.proj 1) =
    capPolynomial coefficients 1 reservoirDot ≫ coefficientExtraction := by
  have heval : capPolynomial coefficients 1 reservoirDot = (-1 : End Plane) + reservoirDot := by
    simp [capPolynomial, Finset.sum_range_succ, coefficients]
  rw [heval]
  apply ModuleCat.hom_ext
  change (LinearMap.proj 1).comp augmentedMap.hom =
    coefficientExtraction.hom.comp (-LinearMap.id + reservoirDot.hom)
  apply LinearMap.ext
  intro z
  simp [augmentedMap, reservoirDot, coefficientExtraction]

#print axioms negative_cap_annihilates_mate
#print axioms negative_cap_unit_window

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some idx := env.header.moduleNames.idxOf?
      `OddMath.QuiverHecke.SwappedVacuum.NegativeCapMoments | throwError "Module not imported"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations: standard axioms only"

end NonVacuity.SwappedNegativeCapMoments
