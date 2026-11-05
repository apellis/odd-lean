/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteNondegeneracy

/-! # The vacuum route hypotheses, field by field

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, in the research scope of `FieldScopeBoundary.md`.

`VacuumRouteHypotheses` asks for one `VacuumRouteSector` at every route index: a
characteristic-zero field, homogeneous scalars, a normalization, a finite colour set
`J`, an equal-weight upward word pair over `J`, an external weight `μ` and a degree
bound `d`. A sector bundles an upward action with a vacuum and raw coefficient action
(the *base*) and four route inputs on that base. This file separates them, so that
each input can be removed from the hypotheses of the end theorem as soon as it is
proved for a fixed choice of bases:

* `VacuumRouteIndex D` and `VacuumRouteBase`: the route indices and the base of a
  sector;
* `PositiveBubbleField`, `NonpositiveBubbleField`, `CoordinateField` and
  `ChartField`: the four inputs at every index, for a fixed choice of bases;
* `VacuumRouteHypotheses.of_fields` and `nondegeneracy_of_vacuum_route_fields`: the
  four fields give the route hypotheses, hence the conjecture.

The statements are reduction steps. For the swapped route bases `swappedRouteBases` the
four fields are proved: `positiveBubbleField_swappedRouteBases`,
`nonpositiveBubbleField_of_entries` with `swappedRightEntriesField`,
`swappedCoordinateField` and `swappedChartField`; the resulting theorem is
`nondegeneracy_of_symmetrizer`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u w

section Base
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- The base of a route sector: an upward module action at `μ` with a vacuum vector
and a raw coefficient action on the source sector `V t`. The modules live in
`Type (u + 1)`, as for the swapped probe-reservoir action. -/
structure VacuumRouteBase (μ : X) (t : List I) where
  A : UpwardModuleAction.{u, u + 1} D Sc μ
  vacuum : A.V t
  raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)

variable {D Sc} {cs : SKM.CScalars Sc} {μ : X} {t t' : List I} {d : ℕ}

/-- A base together with the four route inputs on it is a route sector. -/
def VacuumRouteBase.toSector (B : VacuumRouteBase D Sc μ t)
    (hp : VacuumBubblesPositiveHeight cs B.A t B.raw
      (probeExponent D μ t d) (reservoirLevel D μ t d))
    (hn : VacuumBubblesNonpositiveHeight cs B.A t B.raw
      (probeExponent D μ t d) (reservoirLevel D μ t d))
    (Q : VacuumCoordinates D Sc B.A t t' d)
    (hc : VacuumChartCoherence D Sc Q B.vacuum B.raw) :
    VacuumRouteSector D Sc cs μ t t' d where
  A := B.A
  vacuum := B.vacuum
  raw := B.raw
  bubblesPositive := hp
  bubblesNonpositive := hn
  coordinates := Q
  chart := hc

end Base

variable {I X : Type u} [AddCommGroup X]

/-- **A route index** of `D`: the data over which `VacuumRouteHypotheses` quantifies. -/
structure VacuumRouteIndex (D : SKM.Datum I X) where
  /-- The ground field. -/
  K : Type u
  [field : Field K]
  [charZero : CharZero K]
  /-- Homogeneous scalars over `K`. -/
  Sc : SKM.Scalars D K
  homogeneous : Sc.Homogeneous
  /-- The normalization. -/
  cs : SKM.CScalars Sc
  /-- The finite colour set. -/
  J : Finset I
  /-- The source word. -/
  t : List J
  /-- The target word. -/
  t' : List J
  weight_eq : SKM.wt (D.restrictColours J) 0 (SKM.ups t) =
    SKM.wt (D.restrictColours J) 0 (SKM.ups t')
  /-- The external weight. -/
  μ : X
  /-- The degree bound. -/
  d : ℕ

attribute [instance] VacuumRouteIndex.field VacuumRouteIndex.charZero

namespace VacuumRouteIndex
variable {D : SKM.Datum I X} (ι : VacuumRouteIndex D)

/-- The datum of the sector: the pairing extension of the restriction to `J`. -/
abbrev datum := ReservoirWeights.pairingExtension (D.restrictColours ι.J)

/-- The scalars of the sector. -/
abbrev scalars : SKM.Scalars ι.datum ι.K :=
  ReservoirWeights.pairingExtensionScalars (D.restrictColours ι.J) (ι.Sc.restrictColours D ι.J)

/-- The normalization of the sector. -/
abbrev cscalars : SKM.CScalars ι.scalars :=
  ReservoirWeights.pairingExtensionCScalars (D.restrictColours ι.J)
    (ι.cs.restrictColours D ι.J ι.Sc)

/-- The weight of the sector, `(μ, 0)`. -/
abbrev weight : X × (ι.J → ℤ) := (ι.μ, 0)

end VacuumRouteIndex

/-- **A choice of route bases**: the base of a sector at every route index. -/
def VacuumRouteBases (D : SKM.Datum I X) : Type _ :=
  ∀ ι : VacuumRouteIndex D, VacuumRouteBase ι.datum ι.scalars ι.weight ι.t

variable {D : SKM.Datum I X} (B : VacuumRouteBases D)

/-- **Route field: positive-height bubbles** for the chosen bases. -/
def PositiveBubbleField : Prop :=
  ∀ ι : VacuumRouteIndex D, VacuumBubblesPositiveHeight ι.cscalars (B ι).A ι.t (B ι).raw
    (probeExponent ι.datum ι.weight ι.t ι.d) (reservoirLevel ι.datum ι.weight ι.t ι.d)

/-- **Route field: nonpositive-height bubbles** for the chosen bases. -/
def NonpositiveBubbleField : Prop :=
  ∀ ι : VacuumRouteIndex D, VacuumBubblesNonpositiveHeight ι.cscalars (B ι).A ι.t (B ι).raw
    (probeExponent ι.datum ι.weight ι.t ι.d) (reservoirLevel ι.datum ι.weight ι.t ι.d)

/-- **Route field: vacuum coordinates** for the chosen bases. -/
def CoordinateField : Type _ :=
  ∀ ι : VacuumRouteIndex D, VacuumCoordinates ι.datum ι.scalars (B ι).A ι.t ι.t' ι.d

/-- **Route field: chart coherence** for the chosen bases and coordinates. -/
def ChartField (Q : CoordinateField B) : Prop :=
  ∀ ι : VacuumRouteIndex D, VacuumChartCoherence ι.datum ι.scalars (Q ι) (B ι).vacuum (B ι).raw

/-- The four route fields for one choice of bases give the route hypotheses. -/
theorem VacuumRouteHypotheses.of_fields {sy : SKM.Symmetrizer D}
    (hp : PositiveBubbleField B) (hn : NonpositiveBubbleField B) (Q : CoordinateField B)
    (hc : ChartField B Q) : VacuumRouteHypotheses D sy where
  sectors K _ _ Sc hh cs J tJ t'J hw μ d :=
    let ι : VacuumRouteIndex D := ⟨K, Sc, hh, cs, J, tJ, t'J, hw, μ, d⟩
    ⟨(B ι).toSector (hp ι) (hn ι) (Q ι) (hc ι)⟩

/-- **The conjecture from the four route fields** (Brundan–Ellis, arXiv:1701.04133v2,
§8, in the research scope of `FieldScopeBoundary.md`): for a symmetrizable datum, a
choice of route bases with the four route fields gives the conjecture over every
commutative ring with `2` invertible, for homogeneous scalars. A reduction step of
`nondegeneracy_of_symmetrizer`, where the four fields are proved for the swapped route bases. -/
theorem nondegeneracy_of_vacuum_route_fields {sy : SKM.Symmetrizer D}
    (hp : PositiveBubbleField B) (hn : NonpositiveBubbleField B) (Q : CoordinateField B)
    (hc : ChartField B Q) {R : Type w} [CommRing R] (h₂ : IsUnit (2 : R))
    {Sc : SKM.Scalars D R} (hh : Sc.Homogeneous) (cs : SKM.CScalars Sc) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_vacuum_route (VacuumRouteHypotheses.of_fields (sy := sy) B hp hn Q hc) h₂ hh cs

end OddMath.QuiverHecke
