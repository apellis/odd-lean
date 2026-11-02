import OddMath.QuiverHecke.SwappedVacuum.InverseCapMoments
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! An occupied signed degree-two cap. The probe polynomial is T²+1,
and every signed slide and extraction-window hypothesis is proved. -/
noncomputable section
namespace NonVacuity.SwappedInverseCapSigned
open CategoryTheory OddMath.QuiverHecke.SwappedVacuum

private abbrev Line := ModuleCat.of ℚ ℚ
private abbrev Plane := ModuleCat.of ℚ (Fin 2 → ℚ)

private def probeDot : End Plane := ModuleCat.ofHom
  (LinearMap.pi fun j : Fin 2 => if j = 0 then -LinearMap.proj 1 else LinearMap.proj 0)

private def reservoirDot : End Plane := ModuleCat.ofHom
  (LinearMap.pi fun j : Fin 2 => if j = 0 then LinearMap.proj 1 else 0)

private def unitColumn : Line ⟶ Plane := ModuleCat.ofHom
  (LinearMap.pi fun j : Fin 2 => if j = 0 then 0 else LinearMap.id)

private def coefficientExtraction : Plane ⟶ Line := ModuleCat.ofHom (LinearMap.proj 0)

private def coefficients (n : ℕ) : ℚ := if n = 0 ∨ n = 2 then 1 else 0

private theorem signed_slide :
    (𝟙 Plane) ≫ reservoirDot - (-1 : ℚ) • (probeDot ≫ 𝟙 Plane) =
      coefficientExtraction ≫ unitColumn := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext j
  fin_cases j <;> simp [probeDot, reservoirDot, coefficientExtraction, unitColumn]

private theorem window (a : ℕ) (ha : a < 2) :
    unitColumn ≫ (reservoirDot ^ a) ≫ coefficientExtraction =
      if a + 1 = 2 then 𝟙 Line else 0 := by
  interval_cases a <;> apply ModuleCat.hom_ext <;> apply LinearMap.ext <;> intro z <;>
    simp [unitColumn, reservoirDot, coefficientExtraction, End.one_def]

private theorem probe_relation : capPolynomial coefficients 2 probeDot = 0 := by
  have heval : capPolynomial coefficients 2 probeDot = (1 : End Plane) + probeDot * probeDot := by
    simp [capPolynomial, Finset.sum_range_succ, coefficients, pow_two]
  rw [heval]
  apply ModuleCat.hom_ext
  change LinearMap.id + probeDot.hom.comp probeDot.hom = 0
  apply LinearMap.ext
  intro z
  funext j
  fin_cases j <;> (simp [probeDot]; rfl)

/-- The signed inverse cap is the literal coefficient-extraction row. -/
example : (Iso.refl Plane).inv ≫ coefficientExtraction =
    capPolynomial coefficients 2 reservoirDot ≫ coefficientExtraction := by
  apply principal_inverse_cap (-1 : ℚ) probeDot reservoirDot (Iso.refl Plane)
    unitColumn coefficientExtraction coefficientExtraction 2 (by norm_num) coefficients
  · simp [coefficients]
  · intro n hn
    interval_cases n <;> simp [coefficients]
  · exact signed_slide
  · exact window
  · exact probe_relation

/-- The next right moment is 1, so this check retains the signed dot square. -/
example : unitColumn ≫ reservoirDot ≫ (Iso.refl Plane).inv ≫ coefficientExtraction = 𝟙 Line := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  simp [unitColumn, reservoirDot, coefficientExtraction]

end NonVacuity.SwappedInverseCapSigned
