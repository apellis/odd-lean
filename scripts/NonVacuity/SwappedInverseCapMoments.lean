import OddMath.QuiverHecke.SwappedVacuum.InverseCapMoments
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms

/-! Occupied height-zero inverse caps at probe degrees one and two.
Every slide, polynomial relation and extraction window is proved here.
These examples test the algebraic cap formula, not a full factor action. -/

noncomputable section
namespace NonVacuity.SwappedInverseCapMoments
open CategoryTheory OddMath.QuiverHecke.SwappedVacuum

private abbrev Line := ModuleCat.of ℚ ℚ
private abbrev Plane := ModuleCat.of ℚ (Fin 2 → ℚ)

private def linearCoefficients (n : ℕ) : ℚ := if n = 0 then -1 else if n = 1 then 1 else 0

private def negativeIdentity : Line ≅ Line where
  hom := -𝟙 Line
  inv := -𝟙 Line
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- `P=N=1`, with x=1 and reservoir dot zero. The prescribed inverse cap
is -1, while its fake zeroth right moment remains 1. -/
example : negativeIdentity.inv ≫ 𝟙 Line =
    capPolynomial linearCoefficients 1 (0 : End Line) ≫ 𝟙 Line := by
  apply principal_inverse_cap (1 : ℚ) (𝟙 Line) 0 negativeIdentity
    (𝟙 Line) (𝟙 Line) (𝟙 Line) 1 (by norm_num) linearCoefficients
  · simp [linearCoefficients]
  · intro n hn; simp
  · simp [negativeIdentity]
  · intro a ha
    have : a = 0 := by omega
    subst a; simp
  · simp [capPolynomial, Finset.sum_range_succ, linearCoefficients]

private def probeDot : End Plane := ModuleCat.ofHom
  (LinearMap.pi fun j : Fin 2 => if j = 0 then LinearMap.proj 1 else
    -LinearMap.proj 0 + (2 : ℚ) • LinearMap.proj 1)

private def reservoirDot : End Plane := ModuleCat.ofHom
  (LinearMap.pi fun j : Fin 2 => if j = 0 then LinearMap.proj 1 else 0)

private def unitColumn : Line ⟶ Plane := ModuleCat.ofHom
  (LinearMap.pi fun j : Fin 2 => if j = 0 then 0 else LinearMap.id)

private def capRow : Plane ⟶ Line := ModuleCat.ofHom
  (LinearMap.proj 0 - (2 : ℚ) • LinearMap.proj 1)

private def coefficientExtraction : Plane ⟶ Line := ModuleCat.ofHom (LinearMap.proj 0)

private def quadraticCoefficients (n : ℕ) : ℚ :=
  if n = 0 then 1 else if n = 1 then -2 else if n = 2 then 1 else 0

private theorem quadratic_slide :
    (𝟙 Plane) ≫ reservoirDot - (1 : ℚ) • (probeDot ≫ 𝟙 Plane) =
      capRow ≫ unitColumn := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext j
  fin_cases j
  · simp [probeDot, reservoirDot, capRow, unitColumn]
  · simp [probeDot, reservoirDot, capRow, unitColumn]; ring

private theorem quadratic_window (a : ℕ) (ha : a < 2) :
    unitColumn ≫ (reservoirDot ^ a) ≫ coefficientExtraction =
      if a + 1 = 2 then 𝟙 Line else 0 := by
  interval_cases a <;> apply ModuleCat.hom_ext <;> apply LinearMap.ext <;> intro z <;>
    simp [unitColumn, reservoirDot, coefficientExtraction, End.one_def]

private theorem quadratic_probe : capPolynomial quadraticCoefficients 2 probeDot = 0 := by
  have heval : capPolynomial quadraticCoefficients 2 probeDot =
      (1 : End Plane) + (-2 : ℚ) • probeDot + probeDot * probeDot := by
    simp [capPolynomial, Finset.sum_range_succ, quadraticCoefficients,
      pow_two, End.mul_def, End.one_def]
  rw [heval]
  apply ModuleCat.hom_ext
  change (LinearMap.id + (-2 : ℚ) • probeDot.hom + probeDot.hom.comp probeDot.hom) = 0
  apply LinearMap.ext
  intro z
  funext j
  fin_cases j <;> (simp [probeDot]; ring_nf; rfl)

/-- `P=N=2`, `g(T)=(T-1)^2`: the nonzero nilpotent reservoir dot and the
companion probe dot have the literal rank-one mate slide. The identity
principal inverse recovers the prescribed row `(1,-2)`. -/
example : (Iso.refl Plane).inv ≫ capRow =
    capPolynomial quadraticCoefficients 2 reservoirDot ≫ coefficientExtraction := by
  exact principal_inverse_cap (1 : ℚ) probeDot reservoirDot (Iso.refl Plane)
    unitColumn capRow coefficientExtraction 2 (by norm_num) quadraticCoefficients
    (by simp [quadraticCoefficients]) (by intro n hn; simp)
    quadratic_slide quadratic_window quadratic_probe

example : reservoirDot ≠ 0 := by
  intro h
  have h' := congrArg (fun f : End Plane => f.hom (fun j => if j = 0 then 0 else 1) 0) h
  change (1 : ℚ) = 0 at h'
  norm_num at h'

#print axioms slide_coefficient_window
#print axioms principal_cap_polynomial
#print axioms principal_inverse_cap
#print axioms principal_inverse_right_moment

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.SwappedVacuum.InverseCapMoments then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"

end NonVacuity.SwappedInverseCapMoments
