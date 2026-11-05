/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteSwappedPositiveField
import OddMath.QuiverHecke.VacuumRouteSwappedNonpositiveBubbles

/-! # Reduction of the right vacuum entries to the probe reservoir

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, in the research scope of `FieldScopeBoundary.md`; (2.11), (2.13),
(2.17), (2.18), and `InverseColumnMoments.md`.

The intermediate hypothesis `SwappedRightEntriesField` asks for the vacuum entries of the right
bubbles at nonpositive height (`VacuumRightEntries`) at every route index. This file reduces it
to the same entries for an arbitrary probe reservoir, at its vacuum weight `ΛP - ΛR`, under the
two positivity conditions that hold at every route index:

* `VacuumRouteIndex.probeCutoff_pos`: the probe cutoffs of every route index are positive. In
  particular the probe exponent `M` is positive at every odd colour, so the case `M = 0` of the
  odd entries does not arise;
* `RightVacuumEntrySupply`: the right vacuum entries of every probe reservoir with positive probe
  cutoffs and reservoir levels, at its vacuum weight;
* `swappedRightEntriesField_of_supply`: the supply gives `SwappedRightEntriesField`;
* `nondegeneracy_of_rightVacuumEntrySupply`: the conjecture from the supply.

The supply is an intermediate hypothesis: its six families are the entries of the closed
diagrams of `VacuumRightEntries` on the tensor target family, at negative and at zero height.
-/

noncomputable section

namespace OddMath.QuiverHecke
universe u w

variable {I X : Type u} [AddCommGroup X] {D : SKM.Datum I X}

/-- The probe cutoffs of every route index are positive. -/
theorem VacuumRouteIndex.probeCutoff_pos (ι : VacuumRouteIndex D) (i : ι.J) :
    0 < probeCutoff ι.datum ι.exponent i := by
  have h := (SwappedVacuumParameters.cutoff_bounds (D.restrictColours ι.J) ι.μ ι.t ι.d i).1
  have e := probeExponent_pairingExtension (D.restrictColours ι.J) ι.μ ι.t ι.d
  change 0 < probeCutoff ι.datum (probeExponent _ (ι.μ, 0) ι.t ι.d) i
  rw [e]
  omega

/-- **The right vacuum entries of the probe reservoirs.** For every probe reservoir with positive
probe cutoffs and positive reservoir levels, the vacuum entries of the right bubbles at
nonpositive height, at the vacuum weight `ΛP - ΛR`, with probe exponents `m` and reservoir levels
`cutoff`. Intermediate hypothesis. -/
def RightVacuumEntrySupply : Prop :=
  ∀ {J Y k : Type u} [AddCommGroup Y] [CommRing k] [Fintype J]
    (E : SKM.Datum J Y) (Sc : SKM.Scalars E k) (m cutoff : J → ℕ) (ΛP ΛR : Y)
    (L : J × ℕ → ℕ) (hP : ∀ i, (probeCutoff E m i : ℤ) = E.h i ΛP)
    (hR : ∀ i, (cutoff i : ℤ) = E.h i ΛR) (sy : SKM.Symmetrizer E) (hc : Sc.Homogeneous),
    (∀ i, 0 < probeCutoff E m i) → (∀ i, 0 < cutoff i) →
      SwappedAssembly.SupportedSectors.VacuumRightEntries E Sc m cutoff ΛP ΛR L hP hR sy hc
        (ΛP - ΛR) m cutoff

/-- **The right vacuum entries at every route index** from the right vacuum entries of the probe
reservoirs, transported along `probeHW - reservoirHW = (μ, 0)`. -/
theorem swappedRightEntriesField_of_supply (h : RightVacuumEntrySupply.{u})
    (sy : SKM.Symmetrizer D) : SwappedRightEntriesField sy := fun ι => by
  have e := h ι.datum ι.scalars ι.exponent ι.level ι.probeHW ι.reservoirHW ι.power
    ι.probe_pairing ι.reservoir_pairing (ι.symmetrizer sy) ι.scalars_homogeneous
    ι.probeCutoff_pos ι.level_pos
  rw [ι.weight_difference] at e
  exact e

/-- **The conjecture from the right vacuum entries of the probe reservoirs.** Intermediate: the
supply is open. -/
theorem nondegeneracy_of_rightVacuumEntrySupply (h : RightVacuumEntrySupply.{u})
    (sy : SKM.Symmetrizer D) {R : Type w} [CommRing R] (h₂ : IsUnit (2 : R))
    {Sc : SKM.Scalars D R} (hh : Sc.Homogeneous) (cs : SKM.CScalars Sc) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_swapped_right_entries sy (swappedRightEntriesField_of_supply h sy) h₂ hh cs

end OddMath.QuiverHecke
