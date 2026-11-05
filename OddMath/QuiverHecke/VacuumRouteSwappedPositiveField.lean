/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteSwappedPositiveBubbles
import OddMath.QuiverHecke.SwappedAssembly.SupportedLeftVacuumEntries

/-! # The positive-height bubble field of the swapped route bases

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, in the research scope of `FieldScopeBoundary.md`; (2.11), (2.13),
(2.17), (2.18), and `InverseColumnMoments.md`.

The vacuum entries of the left bubbles and of the odd bubble at positive height
(`SupportedLeftVacuumEntries`) discharge the intermediate hypothesis `SwappedLeftEntriesField`:

* `SupportedSectors.vacuumLeftEntries`: `VacuumLeftEntries` at the vacuum weight of the probe
  reservoir, for positive reservoir levels;
* `VacuumRouteIndex.level_pos`: the reservoir levels of every route index are positive;
* `swappedLeftEntriesField`: the vacuum entries at every route index;
* `positiveBubbleField_swappedRouteBases`: `PositiveBubbleField (swappedRouteBases sy)`;
* `nondegeneracy_of_swapped_right_entries`: the conjecture from the right vacuum entries at
  nonpositive height alone.
-/

noncomputable section

namespace OddMath.QuiverHecke
universe u w

namespace SwappedAssembly.SupportedSectors
open SKM CyclotomicAction ELVOld

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (hF : ProbeActionInputs D Sc m cutoff (PowerWordContent.powerBound D cutoff L) ΛP ΛR hP hR)

include hF in
/-- **Vacuum entries of the bubbles at positive height**, at the vacuum weight `ΛP - ΛR` of the
probe reservoir with exponents `m` and positive reservoir levels `cutoff`. -/
theorem vacuumLeftEntries (hN : ∀ i, 0 < cutoff i) (μ : X) (hμ : ΛP - ΛR = μ) :
    VacuumLeftEntries D Sc m cutoff ΛP ΛR L hP hR hF μ m cutoff := by
  have hw := (tensorVacuumWeight D Sc m cutoff ΛP ΛR L hP hR).trans hμ
  subst hw
  exact ⟨fun i hi h s =>
      vacuumEntry_left_even D Sc m cutoff ΛP ΛR L hP hR hF i hi (hN i) h s,
    fun i hi h s => vacuumEntry_left_odd D Sc m cutoff ΛP ΛR L hP hR hF i hi (hN i) h s,
    fun i h => vacuumEntry_oddBubble D Sc m cutoff ΛP ΛR L hP hR hF i.1 i.2 (hN i.1) h⟩

end SwappedAssembly.SupportedSectors

variable {I X : Type u} [AddCommGroup X] {D : SKM.Datum I X}

/-- The reservoir levels of every route index are positive. -/
theorem VacuumRouteIndex.level_pos (ι : VacuumRouteIndex D) (i : ι.J) : 0 < ι.level i := by
  have h := (SwappedVacuumParameters.cutoff_bounds (D.restrictColours ι.J) ι.μ ι.t ι.d i).2
  have e := congrFun (reservoirLevel_pairingExtension (D.restrictColours ι.J) ι.μ ι.t ι.d) i
  change 0 < reservoirLevel _ (ι.μ, 0) ι.t ι.d i
  rw [e]
  omega

/-- **The vacuum entries of the bubbles at positive height** hold at every route index of the
swapped route bases. -/
theorem swappedLeftEntriesField (sy : SKM.Symmetrizer D) : SwappedLeftEntriesField sy :=
  fun ι => SwappedAssembly.SupportedSectors.vacuumLeftEntries ι.datum ι.scalars ι.exponent
    ι.level ι.probeHW ι.reservoirHW ι.power ι.probe_pairing ι.reservoir_pairing
    (ι.actionInputs sy) ι.level_pos ι.weight ι.weight_difference

/-- **The positive-height bubble field of the swapped route bases.** -/
theorem positiveBubbleField_swappedRouteBases (sy : SKM.Symmetrizer D) :
    PositiveBubbleField (swappedRouteBases sy) :=
  positiveBubbleField_of_entries sy (swappedLeftEntriesField sy)

/-- **The conjecture from the right vacuum entries** of the bubbles at nonpositive height, for
the swapped route bases. The hypothesis `SwappedRightEntriesField` is proved
(`swappedRightEntriesField_of_supply`); the unconditional form is `nondegeneracy_of_symmetrizer`. -/
theorem nondegeneracy_of_swapped_right_entries (sy : SKM.Symmetrizer D)
    (hR : SwappedRightEntriesField sy)
    {R : Type w} [CommRing R] (h₂ : IsUnit (2 : R))
    {Sc : SKM.Scalars D R} (hh : Sc.Homogeneous) (cs : SKM.CScalars Sc) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_swapped_entries sy (swappedLeftEntriesField sy) hR h₂ hh cs

end OddMath.QuiverHecke
