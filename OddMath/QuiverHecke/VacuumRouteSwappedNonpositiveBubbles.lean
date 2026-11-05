/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteSwappedCharts
import OddMath.QuiverHecke.SwappedAssembly.SupportedRightBubbleCoefficients

/-! # Nonpositive-height bubbles of the swapped route bases

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, in the research scope of `FieldScopeBoundary.md`; Definition 2.3,
(2.16)–(2.18), and `SwappedVacuumBubbles.md` §5.

At every route index `ι` the swapped action is the supported action at the weight `(μ, 0)`,
and the raw coefficient action of `ι.swappedBase sy` is the tensor matrix coefficient action at
the source word `ι.t`. So the vacuum entries `SupportedSectors.VacuumRightEntries` of the
closed right bubbles and of the odd bubble at nonpositive height give the right-bubble
hypothesis, and through (5.5)/(5.6) (`VacuumRightBubblesNonpositiveHeight.toNonpositiveHeight`)
the nonpositive-height bubble field:

* `SwappedRightEntriesField sy`: the vacuum entries at every route index;
* `swappedRouteBases_closedAct_cl`: a closed diagram with such a vacuum entry acts as the
  raw coefficient action in the swapped base;
* `nonpositiveBubbleField_of_entries`: `NonpositiveBubbleField (swappedRouteBases sy)`;
* `nondegeneracy_of_swapped_positive_field_and_entries`: the conjecture from the positive
  bubble field and the vacuum entries.

The vacuum entries are an intermediate hypothesis: they are the cap moments of the probe
reservoir at the vacuum sector.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u w

variable {I X : Type u} [AddCommGroup X] {D : SKM.Datum I X}

/-- **The vacuum entries of the right bubbles at nonpositive height**, at every route index of
the swapped route bases. Intermediate hypothesis. -/
def SwappedRightEntriesField (sy : SKM.Symmetrizer D) : Prop :=
  ∀ ι : VacuumRouteIndex D,
    SwappedAssembly.SupportedSectors.VacuumRightEntries (D := ι.datum) (Sc := ι.scalars)
      (m := ι.exponent) (cutoff := ι.level) (ΛP := ι.probeHW) (ΛR := ι.reservoirHW)
      (L := ι.power) (hP := ι.probe_pairing) (hR := ι.reservoir_pairing)
      (hF := ι.actionInputs sy) ι.weight
      (probeExponent ι.datum ι.weight ι.t ι.d) (reservoirLevel ι.datum ι.weight ι.t ι.d)

/-- At a route index, a closed diagram whose vacuum entry is the coefficient action of `a`
acts in the swapped base as the raw coefficient action of `a`. -/
theorem swappedRouteBases_closedAct_cl (sy : SKM.Symmetrizer D) (ι : VacuumRouteIndex D)
    (M : List (SKM.LayerData ι.J)) (hM : SKM.SChain [] M []) (a : SKM.SYM ι.datum ι.K)
    (h : SwappedAssembly.SupportedSectors.VacuumEntry (D := ι.datum)
      (Sc := ι.scalars) (m := ι.exponent) (cutoff := ι.level) (ΛP := ι.probeHW)
      (ΛR := ι.reservoirHW) (L := ι.power) (hP := ι.probe_pairing)
      (hR := ι.reservoir_pairing) (hF := ι.actionInputs sy)
      ι.weight M hM a) :
    (swappedRouteBases sy ι).A.closedAct ι.t (SKM.cl ι.datum ι.scalars ι.weight [] [] M) =
      (swappedRouteBases sy ι).raw a :=
  SwappedAssembly.SupportedSectors.closedAct_cl_eq_coefficient (D := ι.datum)
      (Sc := ι.scalars) (m := ι.exponent) (cutoff := ι.level) (ΛP := ι.probeHW)
      (ΛR := ι.reservoirHW) (L := ι.power) (hP := ι.probe_pairing)
      (hR := ι.reservoir_pairing) (hF := ι.actionInputs sy)
      (sw := ι.t) ι.weight ι.t M hM a h

/-- **The nonpositive-height bubble field of the swapped route bases**, from the vacuum entries
of the right bubbles. -/
theorem nonpositiveBubbleField_of_entries (sy : SKM.Symmetrizer D)
    (hE : SwappedRightEntriesField sy) : NonpositiveBubbleField (swappedRouteBases sy) :=
  fun ι =>
    (VacuumRightBubblesNonpositiveHeight.of_closed ι.cscalars (swappedRouteBases sy ι).A ι.t
      (swappedRouteBases sy ι).raw _ _
      (fun i hi h s => swappedRouteBases_closedAct_cl sy ι _ _ _ ((hE ι).neg_even i hi h s))
      (fun i hi h s => swappedRouteBases_closedAct_cl sy ι _ _ _ ((hE ι).zero_even i hi h s))
      (fun i hi h s => swappedRouteBases_closedAct_cl sy ι _ _ _ ((hE ι).neg_odd i hi h s))
      (fun i hi h s => swappedRouteBases_closedAct_cl sy ι _ _ _ ((hE ι).zero_odd i hi h s))
      (fun i h => swappedRouteBases_closedAct_cl sy ι _ _ _ ((hE ι).odd_neg i h))
      (fun i h => swappedRouteBases_closedAct_cl sy ι _ _ _
        ((hE ι).odd_zero i h))).toNonpositiveHeight

/-- **The conjecture from the positive bubble field and the vacuum entries** of the right
bubbles at nonpositive height, for the swapped route bases. A reduction step: both inputs
are proved (`positiveBubbleField_swappedRouteBases`, `swappedRightEntriesField`), and the
resulting theorem is `nondegeneracy_of_symmetrizer`. -/
theorem nondegeneracy_of_swapped_positive_field_and_entries (sy : SKM.Symmetrizer D)
    (hp : PositiveBubbleField (swappedRouteBases sy)) (hE : SwappedRightEntriesField sy)
    {R : Type w} [CommRing R] (h₂ : IsUnit (2 : R))
    {Sc : SKM.Scalars D R} (hh : Sc.Homogeneous) (cs : SKM.CScalars Sc) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_swapped_bubble_fields sy hp (nonpositiveBubbleField_of_entries sy hE) h₂ hh cs

end OddMath.QuiverHecke
