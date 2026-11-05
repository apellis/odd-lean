/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteSwappedBases
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCornerEvaluation
import OddMath.QuiverHecke.SwappedVacuum.TransformedIdeal
import OddMath.SKM.ELVCoefficientPowers

/-! # Chart coherence of the swapped route bases

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, in the research scope of `FieldScopeBoundary.md`;
`SwappedVacuumCoordinates.md` §§2–7.

For a symmetrizer `sy`, at every route index `ι` the corner evaluation of the swapped
action (`SupportedSectors.tensorCornerEvaluation`) is transported along
`probeHW - reservoirHW = (μ, 0)` to the base `ι.swappedBase sy`. Its ideal at the target
word is the transformed ideal of the elementary powers `e_j ^ coefficientPower`, each of
coefficient weight at least `vacuumCutoff t d`; so the ideal lies in the vacuum window
(`transformedIdeal_le_vacuumWindow`). This gives

* `swappedCoordinateField sy : CoordinateField (swappedRouteBases sy)`, and
* `swappedChartField sy : ChartField (swappedRouteBases sy) (swappedCoordinateField sy)`,

with no hypothesis beyond the route index; `nondegeneracy_of_swapped_bubble_fields`
reduces the conjecture to the two bubble fields of these bases.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u w

variable {I X : Type u} [AddCommGroup X] {D : SKM.Datum I X}

namespace VacuumRouteIndex
variable (ι : VacuumRouteIndex D) (sy : SKM.Symmetrizer D)

/-- The corner evaluation of the swapped action of the sector at a weight `w` equal to
`probeHW - reservoirHW`, with the transported tensor matrix vacuum. -/
def cornerEvaluationAt (w : X × (ι.J → ℤ)) (h : ι.probeHW - ι.reservoirHW = w) :
    VacuumCornerEvaluation ι.datum ι.scalars (ι.actionAt sy w) ι.t
      (SwappedAssembly.SupportedSectors.tensorMatrixCoefficientAction ι.datum ι.scalars
        ι.exponent ι.level ι.probeHW ι.reservoirHW ι.power ι.t
        (SKM.ob ι.datum w (upWord ι.t)))
      (cast (congrArg (fun w => (ι.actionAt sy w).V ι.t) h)
        (SwappedAssembly.SupportedSectors.tensorMatrixVacuum ι.datum ι.scalars ι.exponent
          ι.level ι.probeHW ι.reservoirHW ι.power ι.t)) := by
  subst h
  exact SwappedAssembly.SupportedSectors.tensorCornerEvaluation ι.datum ι.scalars ι.exponent
    ι.level ι.probeHW ι.reservoirHW ι.power ι.probe_pairing ι.reservoir_pairing ι.t
    (ι.actionInputs sy)

/-- The ideal of the transported corner evaluation is the transformed ideal of the
elementary powers. -/
theorem cornerEvaluationAt_K (w : X × (ι.J → ℤ)) (h : ι.probeHW - ι.reservoirHW = w)
    (t' : List ι.J) :
    (ι.cornerEvaluationAt sy w h).K t' =
      PowerWordQuotientCoordinates.kernel ι.datum ι.scalars ι.level ι.power ι.t t' := by
  subst h
  rfl

/-- **The corner evaluation of the swapped base** of the sector. -/
def swappedCornerEvaluation :
    VacuumCornerEvaluation ι.datum ι.scalars (ι.swappedBase sy).A ι.t (ι.swappedBase sy).raw
      (ι.swappedBase sy).vacuum :=
  ι.cornerEvaluationAt sy ι.weight ι.weight_difference

/-- The elementary powers of the tensor families have coefficient weight at least the
vacuum cutoff. -/
theorem power_mem_coefficientAtLeast :
    ∀ a ∈ Set.range (fun j : ι.J × ℕ => SKM.SYM.e ι.datum ι.K j.1 j.2 ^ ι.power j),
      a ∈ SKM.SYM.CoefficientAtLeast ι.datum ι.K (vacuumCutoff ι.t ι.d) := by
  rintro _ ⟨j, rfl⟩
  exact SKM.SYM.coefficientAtLeast_antitone ι.datum ι.K
    (SwappedVacuumParameters.coefficientPower_weight ι.datum ι.t ι.d j)
    (SKM.SYM.elementary_pow_mem_coefficientAtLeast ι.datum ι.K j _)

/-- The ideal of the swapped corner evaluation lies in the vacuum window. -/
theorem swappedCornerEvaluation_ideal_le :
    (ι.swappedCornerEvaluation sy).K ι.t' ≤ ExtendedAtLeast ι.datum ι.scalars ι.t ι.t'
      ((vacuumCutoff ι.t ι.d : ℤ) - 2 * ι.t.length.choose 2) := by
  change (ι.cornerEvaluationAt sy ι.weight ι.weight_difference).K ι.t' ≤ _
  rw [cornerEvaluationAt_K]
  exact transformedIdeal_le_vacuumWindow ι.datum ι.scalars ι.weight ι.t ι.t' ι.d
    (ι.power_mem_coefficientAtLeast)

end VacuumRouteIndex

/-- **Vacuum coordinates of the swapped route bases**: the coordinates of the swapped
corner evaluation at the target word. -/
def swappedCoordinateField (sy : SKM.Symmetrizer D) : CoordinateField (swappedRouteBases sy) :=
  fun ι => (ι.swappedCornerEvaluation sy).coordinates ι.t' ι.d
    (ι.swappedCornerEvaluation_ideal_le sy)

/-- **Chart coherence of the swapped route bases**: the route field `ChartField` holds
for the swapped bases and their corner-evaluation coordinates. -/
theorem swappedChartField (sy : SKM.Symmetrizer D) :
    ChartField (swappedRouteBases sy) (swappedCoordinateField sy) :=
  fun ι => (ι.swappedCornerEvaluation sy).chartCoherence ι.t' ι.d
    (ι.swappedCornerEvaluation_ideal_le sy)

/-- **The conjecture from the two bubble fields of the swapped bases** (Brundan–Ellis,
arXiv:1701.04133v2, §8, in the research scope of `FieldScopeBoundary.md`): the
coordinate and chart fields of `swappedRouteBases sy` are discharged, so the
positive- and nonpositive-height bubble fields of these bases give the conjecture over
every commutative ring with `2` invertible, for homogeneous scalars. A reduction step:
the bubble fields are proved (`positiveBubbleField_swappedRouteBases` and
`nonpositiveBubbleField_of_entries`), and the resulting theorem is
`nondegeneracy_of_symmetrizer`. -/
theorem nondegeneracy_of_swapped_bubble_fields (sy : SKM.Symmetrizer D)
    (hp : PositiveBubbleField (swappedRouteBases sy))
    (hn : NonpositiveBubbleField (swappedRouteBases sy))
    {R : Type w} [CommRing R] (h₂ : IsUnit (2 : R))
    {Sc : SKM.Scalars D R} (hh : Sc.Homogeneous) (cs : SKM.CScalars Sc) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_vacuum_route_fields (sy := sy) (swappedRouteBases sy) hp hn
    (swappedCoordinateField sy) (swappedChartField sy) h₂ hh cs

end OddMath.QuiverHecke
