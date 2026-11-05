/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedVacuumCornerEvaluation
import OddMath.QuiverHecke.VacuumRouteNondegeneracy

/-! # Chart coherence from a corner evaluation

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, in
the research scope of `FieldScopeBoundary.md`; `SwappedVacuumCoordinates.md` (7).

A corner evaluation `E` of an upward module action at the source word `t`
(`VacuumCornerEvaluation`) supplies vacuum coordinates at every target word `t'` whose
ideal satisfies the weight bound: the ideal `E.K t'` and the evaluation `E.ev t'`.
For these coordinates, the chart-coherence route hypothesis `VacuumChartCoherence` is
exactly the vacuum evaluation `VacuumCornerEvaluation.vacuum_evaluation` at the
substituted coefficient `θ(a)`, since substitution acts on the source coefficient only.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k}

namespace VacuumCornerEvaluation
variable {μ : X} {A : UpwardModuleAction D Sc μ} {t : List I}
  {raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)} {vacuum : A.V t}
  (E : VacuumCornerEvaluation D Sc A t raw vacuum)

/-- The vacuum coordinates of a corner evaluation at the target word `t'`. -/
def coordinates (t' : List I) (d : ℕ)
    (ideal_le : E.K t' ≤ ExtendedAtLeast D Sc t t'
      ((vacuumCutoff t d : ℤ) - 2 * t.length.choose 2)) :
    VacuumCoordinates D Sc A t t' d where
  ideal := E.K t'
  ideal_le := ideal_le
  coordinate := E.ev t'

/-- **Chart coherence from a corner evaluation.** For the coordinates of a corner
evaluation, the route hypothesis `VacuumChartCoherence` holds. -/
theorem chartCoherence (t' : List I) (d : ℕ)
    (ideal_le : E.K t' ≤ ExtendedAtLeast D Sc t t'
      ((vacuumCutoff t d : ℤ) - 2 * t.length.choose 2)) :
    VacuumChartCoherence D Sc (E.coordinates t' d ideal_le) vacuum raw where
  evaluation a f := by
    rw [coefficientSubstitution_source]
    exact E.vacuum_evaluation _ f

end VacuumCornerEvaluation

end OddMath.QuiverHecke
