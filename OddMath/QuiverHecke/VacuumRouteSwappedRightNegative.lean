/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteSwappedRightField
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumRightEntriesOdd

/-! # The right vacuum entries at negative height

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, in the research scope of `FieldScopeBoundary.md`; (2.11), (2.13),
(2.17), (2.18), and `InverseColumnMoments.md`.

The odd fields `neg_odd` and `odd_neg` of `VacuumRightNegativeEntries` are
`vacuumEntry_neg_odd` and `vacuumEntry_odd_neg`. The even field `neg_even` is collected in
`RightNegativeEvenSupply`:

* `SupportedSectors.vacuumRightNegativeEntries_of_even`: `VacuumRightNegativeEntries` from the
  even entries at negative height;
* `rightVacuumEntrySupply_of_evenSupply`: `RightVacuumEntrySupply` from the even supply;
* `swappedRightEntriesField_of_evenSupply`: `SwappedRightEntriesField`;
* `nondegeneracy_of_rightNegativeEvenSupply`: the conjecture from the even supply.

`RightNegativeEvenSupply` is an intermediate hypothesis: the even rightward vacuum entries at
negative height.
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
  (sy : Symmetrizer D) (hc : Sc.Homogeneous)
set_option quotPrecheck false
local notation "ν₀" => (elvProbeReservoir D Sc m cutoff (PowerWordContent.powerBound D cutoff L)
  ΛP ΛR hP hR).wt ((0, 0) : Sector I)

/-- **The even right vacuum entries at negative height** of one probe reservoir: the field
`neg_even` of `VacuumRightNegativeEntries`. -/
def VacuumRightNegativeEven : Prop :=
  ∀ i, D.parity i = 0 → 0 < probeCutoff D m i → D.h i ν₀ < 0 → ∀ s : ℕ,
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR sy hc ν₀
      (SKM.etaL i ((s : ℤ) - D.h i ν₀ - 1).toNat ++ SKM.dcapL i (-D.h i ν₀ - 1).toNat)
      ((SKM.sChain_etaL i _).append (SKM.sChain_dcapL i _))
      (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)))

/-- **The right vacuum entries at negative height** from the even ones; the odd entries are
`vacuumEntry_neg_odd` and `vacuumEntry_odd_neg`. -/
theorem vacuumRightNegativeEntries_of_even
    (hev : VacuumRightNegativeEven D Sc m cutoff ΛP ΛR L hP hR sy hc) :
    VacuumRightNegativeEntries D Sc m cutoff ΛP ΛR L hP hR sy hc :=
  ⟨hev,
    fun i hi hP0 hh s => vacuumEntry_neg_odd D Sc m cutoff ΛP ΛR L hP hR sy hc i hi hP0 hh s,
    fun i hP0 hh => vacuumEntry_odd_neg D Sc m cutoff ΛP ΛR L hP hR sy hc cutoff i hP0 hh rfl⟩

end SwappedAssembly.SupportedSectors

/-- **The even right vacuum entries of the probe reservoirs** at negative height. Intermediate
hypothesis. -/
def RightNegativeEvenSupply : Prop :=
  ∀ {J Y k : Type u} [AddCommGroup Y] [CommRing k] [Fintype J]
    (E : SKM.Datum J Y) (Sc : SKM.Scalars E k) (m cutoff : J → ℕ) (ΛP ΛR : Y)
    (L : J × ℕ → ℕ) (hP : ∀ i, (probeCutoff E m i : ℤ) = E.h i ΛP)
    (hR : ∀ i, (cutoff i : ℤ) = E.h i ΛR) (sy : SKM.Symmetrizer E) (hc : Sc.Homogeneous),
    SwappedAssembly.SupportedSectors.VacuumRightNegativeEven E Sc m cutoff ΛP ΛR L hP hR sy hc

/-- **The right vacuum entries of the probe reservoirs** from the even entries at negative
height. Intermediate: the even supply is open. -/
theorem rightVacuumEntrySupply_of_evenSupply (h : RightNegativeEvenSupply.{u}) :
    RightVacuumEntrySupply.{u} := by
  apply rightVacuumEntrySupply_of_negative
  intro J Y k _ _ _ E Sc m cutoff ΛP ΛR L hP hR sy hc
  exact SwappedAssembly.SupportedSectors.vacuumRightNegativeEntries_of_even E Sc m cutoff ΛP ΛR
    L hP hR sy hc (h E Sc m cutoff ΛP ΛR L hP hR sy hc)

variable {I X : Type u} [AddCommGroup X] {D : SKM.Datum I X}

/-- **The right vacuum entries at every route index** from the even entries at negative height.
Intermediate: the even supply is open. -/
theorem swappedRightEntriesField_of_evenSupply (h : RightNegativeEvenSupply.{u})
    (sy : SKM.Symmetrizer D) : SwappedRightEntriesField sy :=
  swappedRightEntriesField_of_supply (rightVacuumEntrySupply_of_evenSupply h) sy

/-- **The conjecture from the even right vacuum entries at negative height.** Intermediate: the
even supply is open. -/
theorem nondegeneracy_of_rightNegativeEvenSupply (h : RightNegativeEvenSupply.{u})
    (sy : SKM.Symmetrizer D) {R : Type w} [CommRing R] (h₂ : IsUnit (2 : R))
    {Sc : SKM.Scalars D R} (hh : Sc.Homogeneous) (cs : SKM.CScalars Sc) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_rightVacuumEntrySupply (rightVacuumEntrySupply_of_evenSupply h) sy h₂ hh cs

end OddMath.QuiverHecke
