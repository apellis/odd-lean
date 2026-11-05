/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedVacuumBlock
import OddMath.QuiverHecke.SwappedVacuumAdjunctionBubbles
import OddMath.QuiverHecke.PairingExtensionRecovery
import OddMath.QuiverHecke.FiniteColourNondegeneracy
import OddMath.SKM.GroundRingNondegeneracy

/-! # The odd Nondegeneracy Conjecture from the vacuum route hypotheses

Research issue #345, toward the Nondegeneracy Conjecture of Brundan–Ellis,
*Super Kac–Moody 2-categories* (arXiv:1701.04133v2), §8, in the scope of
`docs/Nondegeneracy/FieldScopeBoundary.md`: symmetrizable data, homogeneous
scalars, commutative ground rings in which `2` is invertible.

This file assembles the checked reductions into one conditional statement,
`nondegeneracy_of_vacuum_route`. Its proof is
* the ground-ring descent `SKM.nondegeneracyConjecture_of_charZeroField`, reducing
  to fields of characteristic zero;
* the finite-colour reduction `nondegeneracy_of_restrictColours_upward`;
* the pairing-extension recovery
  `PairingExtension.upwardCoefficientMap_injective_of_pairingExtension`
  (vacuum evaluations of the extension `Dₑ` at the weights `(μ, 0)` suffice);
* the bounded vacuum recovery `upwardCoefficientMap_injective_of_vacuum_evaluations`,
  fed through `SwappedVacuumBlock.toSwappedVacuumEvaluation`, which packages
  `UpwardModuleAction.toSwappedVacuumEvaluation`.

The inputs about the constructed swapped action are recorded as the fields of
`VacuumRouteSector`, split by the topic that discharges them:
* `VacuumBubblesPositiveHeight`: the left-bubble generating series at colours
  with `hᵢ(μ) > 0`, even and odd, and the odd bubble there;
* `VacuumBubblesNonpositiveHeight`: the same at colours with `hᵢ(μ) ≤ 0`;
* `VacuumCoordinates`: the quotient ideal of the vacuum coordinates with its
  weight bound, and the coordinate map on the target sector (the vacuum
  coefficient quotient class);
* `VacuumChartCoherence`: the literal evaluation of every presented upward
  diagram at the reservoir-shifted vacuum (regular-probe chart coherence).

The statement is a reduction step: for the swapped route bases the four inputs are
proved (`VacuumRouteFields`, `VacuumRouteSwappedCharts`, `VacuumRouteSwappedPositiveField`,
`VacuumRouteSwappedRightNegative`), which gives `nondegeneracy_of_symmetrizer`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u w

section CommRing
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k} (cs : SKM.CScalars Sc)

/-- **Route hypothesis: bubbles at positive heights.** At colours `i` with
`hᵢ(μ) > 0`, the normalized left bubbles of the upward action `A`, on the source
sector `V t`, act through the raw coefficient action `raw` as the coefficients of
the substituted series: `E_i(-z)/(1-z)^(M_i)` at even colours and
`C_i(-z)/(1+z)^(M_i)` at odd colours, and the odd bubble acts as
`(-1)^(N_i+1) δ_i`. For the swapped action these are the inverse-column moments of
the positive-height vacuum adjunction, computed at the tensor vacuum
(`SwappedVacuum/InverseColumnOddSeries`, `InverseColumnEvenSeries`); what remains is
their attachment to the cup and cap images of the constructed action. -/
structure VacuumBubblesPositiveHeight {μ : X} (A : UpwardModuleAction.{u, w} D Sc μ)
    (t : List I) (raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)) (M N : I → ℕ) : Prop where
  left_even : ∀ i, D.parity i = 0 → 0 < D.h i μ → ∀ s : ℕ,
    A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ s) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i)))
  left_odd : ∀ i, D.parity i = 1 → 0 < D.h i μ → ∀ s : ℕ,
    A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ (2 * s)) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i)))
  oddBubble : ∀ i : {i : I // D.parity i = 1}, 0 < D.h i.1 μ →
    A.closedAct t (SKM.oddBubble cs i μ) = raw (SKM.SYM.probeSign D k N i • SKM.SYM.delta D k i)

/-- **Route hypothesis: bubbles at nonpositive heights.** The same values as in
`VacuumBubblesPositiveHeight`, at colours `i` with `hᵢ(μ) ≤ 0`. There the leftward
cup is the chosen inverse of the vacuum adjunction, so the left series is the
reciprocal of the series computed from the inverse rows; discharging this needs the
nonpositive-height inverse rows of the constructed action, in both parities. -/
structure VacuumBubblesNonpositiveHeight {μ : X} (A : UpwardModuleAction.{u, w} D Sc μ)
    (t : List I) (raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)) (M N : I → ℕ) : Prop where
  left_even : ∀ i, D.parity i = 0 → D.h i μ ≤ 0 → ∀ s : ℕ,
    A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ s) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i)))
  left_odd : ∀ i, D.parity i = 1 → D.h i μ ≤ 0 → ∀ s : ℕ,
    A.closedAct t ((↑(cs.c μ i)⁻¹ : k) • SKM.bubLs cs i μ (2 * s)) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i)))
  oddBubble : ∀ i : {i : I // D.parity i = 1}, D.h i.1 μ ≤ 0 →
    A.closedAct t (SKM.oddBubble cs i μ) = raw (SKM.SYM.probeSign D k N i • SKM.SYM.delta D k i)

variable {cs} in
/-- The two height ranges together give the left-bubble series at every colour. -/
theorem adjunctionBubbleSeries_of_heights {μ : X} {A : UpwardModuleAction.{u, w} D Sc μ}
    {t : List I} {raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)} {M N : I → ℕ}
    (hp : VacuumBubblesPositiveHeight cs A t raw M N)
    (hn : VacuumBubblesNonpositiveHeight cs A t raw M N) :
    AdjunctionBubbleSeries cs A t raw M N where
  left_even i hi s := by
    rcases lt_or_ge 0 (D.h i μ) with h | h
    · exact hp.left_even i hi h s
    · exact hn.left_even i hi h s
  left_odd i hi s := by
    rcases lt_or_ge 0 (D.h i μ) with h | h
    · exact hp.left_odd i hi h s
    · exact hn.left_odd i hi h s
  oddBubble i := by
    rcases lt_or_ge 0 (D.h i.1 μ) with h | h
    · exact hp.oddBubble i h
    · exact hn.oddBubble i h

variable (D Sc) in
/-- **Route hypothesis: the vacuum coefficient quotient class.** A quotient of the
coefficient Hom space `coefficientObj t ⟶ coefficientObj t'` by an ideal of weight
at least `N₀ - 2·C(|t|, 2)` (`N₀ = vacuumCutoff t d`), with a linear coordinate map
from the target sector `V t'` to it. For the swapped action the ideal is the
transformed last-boundary ideal and the coordinates are the canonical tensor-word
quotient observation of the vacuum. -/
structure VacuumCoordinates {μ : X} (A : UpwardModuleAction.{u, w} D Sc μ)
    (t t' : List I) (d : ℕ) where
  ideal : Submodule k (coefficientObj D Sc t ⟶ coefficientObj D Sc t')
  ideal_le : ideal ≤ ExtendedAtLeast D Sc t t'
    ((vacuumCutoff t d : ℤ) - 2 * t.length.choose 2)
  coordinate : A.V t' →ₗ[k] ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸ ideal)

variable (D Sc) in
/-- **Route hypothesis: chart coherence of the vacuum evaluation.** Every presented
upward diagram `f : E_t 1_μ ⟶ E_t' 1_μ`, applied to the reservoir coefficient
`θ(a)` of the vacuum and read in the coordinates `Q`, gives the class of the placed,
substituted source coefficient of `a • f`. At the identity diagram this is the
coefficient class of the vacuum; for general `f` it is the compatibility of the
global and local contextual layer charts with the regular probe, retaining the dot
and both crossing maps. -/
structure VacuumChartCoherence {μ : X} {A : UpwardModuleAction.{u, w} D Sc μ}
    {t t' : List I} {d : ℕ} (Q : VacuumCoordinates D Sc A t t' d) (vacuum : A.V t)
    (raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)) : Prop where
  evaluation : ∀ (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')),
    Q.coordinate (A.act t t' ((alpha D Sc μ).map f)
        (raw (vacuumSubstitution D k μ t d a) vacuum)) =
      Q.ideal.mkQ (placementSign D Sc t t'
        (coefficientSubstitution D Sc (vacuumSubstitution D k μ t d) t t'
          (sourceCoefficientHom D Sc a f)))

variable (D Sc) in
/-- **The vacuum route at one sector**: an upward module action at `μ` with a vacuum
and raw coefficient action on the source sector `V t`, satisfying the four route
hypotheses at the schedule of `SwappedVacuumBlock` (probe exponents
`probeExponent D μ t d`, reservoir levels `reservoirLevel D μ t d`). -/
structure VacuumRouteSector (μ : X) (t t' : List I) (d : ℕ) where
  A : UpwardModuleAction.{u, w} D Sc μ
  vacuum : A.V t
  raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)
  bubblesPositive : VacuumBubblesPositiveHeight cs A t raw
    (probeExponent D μ t d) (reservoirLevel D μ t d)
  bubblesNonpositive : VacuumBubblesNonpositiveHeight cs A t raw
    (probeExponent D μ t d) (reservoirLevel D μ t d)
  coordinates : VacuumCoordinates D Sc A t t' d
  chart : VacuumChartCoherence D Sc coordinates vacuum raw

namespace VacuumRouteSector
variable {cs} {μ : X} {t t' : List I} {d : ℕ}

/-- A route sector is a vacuum block: (A16) follows from the bubble series by the
infinite Grassmannian relations (`AdjunctionBubbleSeries.bubbles_eq`). -/
def toSwappedVacuumBlock (S : VacuumRouteSector D Sc cs μ t t' d) :
    SwappedVacuumBlock D Sc cs μ t t' d where
  A := S.A
  vacuum := S.vacuum
  raw := S.raw
  bubbles_eq := (adjunctionBubbleSeries_of_heights S.bubblesPositive S.bubblesNonpositive).bubbles_eq
  ideal := S.coordinates.ideal
  ideal_le := S.coordinates.ideal_le
  coordinate := S.coordinates.coordinate
  evaluation := S.chart.evaluation

end VacuumRouteSector

end CommRing

section Field
variable {I X k : Type u} [AddCommGroup X] [Field k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

/-- **Field form of the vacuum route.** Over a field, route sectors for the pairing
extension of every finite-colour restriction of `D`, at the weights `(μ, 0)`, for
every equal-weight pair of upward words and every degree bound, imply the
Nondegeneracy Conjecture for `D`. -/
theorem nondegeneracy_of_vacuum_route_sectors
    (h : ∀ (J : Finset I) (tJ t'J : List J),
      SKM.wt (D.restrictColours J) 0 (SKM.ups tJ) =
        SKM.wt (D.restrictColours J) 0 (SKM.ups t'J) →
      ∀ (μ : X) (d : ℕ), Nonempty (VacuumRouteSector.{u, w}
        (ReservoirWeights.pairingExtension (D.restrictColours J))
        (ReservoirWeights.pairingExtensionScalars (D.restrictColours J) (Sc.restrictColours D J))
        (ReservoirWeights.pairingExtensionCScalars (D.restrictColours J)
          (cs.restrictColours D J Sc)) (μ, 0) tJ t'J d)) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_restrictColours_upward D Sc cs fun J tJ t'J hw μ =>
    PairingExtension.upwardCoefficientMap_injective_of_pairingExtension _ _ _ μ tJ t'J
      (upwardCoefficientMap_injective_of_vacuum_evaluations (μ, 0) tJ t'J fun d =>
        (h J tJ t'J hw μ d).map fun S => S.toSwappedVacuumBlock.toSwappedVacuumEvaluation)

end Field

variable {I X : Type u} [AddCommGroup X]

/-- **The vacuum route hypotheses** for a symmetrizable datum `D`: over every field
of characteristic zero, for every homogeneous scalar system and every normalization,
route sectors exist for the pairing extension of every finite-colour restriction, at
every external weight `(μ, 0)`, equal-weight upward word pair and degree bound. The
symmetrizer records the research scope: the route is to be completed for
symmetrizable data only. The sector modules live in `Type (u + 1)`, as do the
modules of the swapped probe-reservoir action. -/
structure VacuumRouteHypotheses (D : SKM.Datum I X) (sy : SKM.Symmetrizer D) : Prop where
  sectors : ∀ (K : Type u) [Field K] [CharZero K] (Sc : SKM.Scalars D K), Sc.Homogeneous →
    ∀ (cs : SKM.CScalars Sc) (J : Finset I) (tJ t'J : List J),
      SKM.wt (D.restrictColours J) 0 (SKM.ups tJ) =
        SKM.wt (D.restrictColours J) 0 (SKM.ups t'J) →
      ∀ (μ : X) (d : ℕ), Nonempty (VacuumRouteSector.{u, u + 1}
        (ReservoirWeights.pairingExtension (D.restrictColours J))
        (ReservoirWeights.pairingExtensionScalars (D.restrictColours J) (Sc.restrictColours D J))
        (ReservoirWeights.pairingExtensionCScalars (D.restrictColours J)
          (cs.restrictColours D J Sc)) (μ, 0) tJ t'J d)

/-- The route hypotheses give the conjecture over every field of characteristic zero. -/
theorem VacuumRouteHypotheses.charZeroFieldNondegeneracy {D : SKM.Datum I X}
    {sy : SKM.Symmetrizer D} (H : VacuumRouteHypotheses D sy) :
    SKM.CharZeroFieldNondegeneracy D := fun K _ _ Sc hh cs =>
  nondegeneracy_of_vacuum_route_sectors D Sc cs (H.sectors K Sc hh cs)

/-- **The odd/mixed Nondegeneracy Conjecture from the vacuum route hypotheses**
(Brundan–Ellis, arXiv:1701.04133v2, §8, in the research scope of
`FieldScopeBoundary.md`). For a symmetrizable datum `D` satisfying the route
hypotheses `VacuumRouteHypotheses D sy`, the conjecture holds over every commutative
ring in which `2` is invertible, for every homogeneous scalar system and every
normalization. A reduction step: the route hypotheses hold for the swapped route bases,
and the resulting statement without them is `nondegeneracy_of_symmetrizer`. -/
theorem nondegeneracy_of_vacuum_route {D : SKM.Datum I X} {sy : SKM.Symmetrizer D}
    (H : VacuumRouteHypotheses D sy) {R : Type w} [CommRing R] (h₂ : IsUnit (2 : R))
    {Sc : SKM.Scalars D R} (hh : Sc.Homogeneous) (cs : SKM.CScalars Sc) :
    SKM.NondegeneracyConjecture cs :=
  SKM.nondegeneracyConjecture_of_charZeroField H.charZeroFieldNondegeneracy h₂ hh cs

end OddMath.QuiverHecke
