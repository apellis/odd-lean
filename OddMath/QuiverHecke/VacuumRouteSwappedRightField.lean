/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteSwappedNonpositiveField
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumZeroHeightEntries

/-! # Assembly of the right vacuum entries at nonpositive height

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, in the research scope of `FieldScopeBoundary.md`; (2.11), (2.13),
(2.17), (2.18), and `InverseColumnMoments.md`.

The six families of `VacuumRightEntries` split by the vacuum height `h`. The three families at
`h = 0` hold for every probe reservoir with positive reservoir levels
(`SupportedVacuumZeroHeightEntries`). The three families at `h < 0` (`neg_even`, `neg_odd`,
`odd_neg`) are collected in `VacuumRightNegativeEntries`, stated at the vacuum weight of the probe
reservoir with the positivity of the probe cutoffs available:

* `SupportedSectors.vacuumRightEntries_of_negative`: `VacuumRightEntries` at the vacuum weight
  from the negative-height families;
* `rightVacuumEntrySupply_of_negative`: `RightVacuumEntrySupply` from the negative-height
  families of every probe reservoir.

`VacuumRightNegativeEntries` is an intermediate hypothesis: its fields are the even and odd
rightward moments at negative height.
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
set_option quotPrecheck false
local notation "ν₀" => (elvProbeReservoir D Sc m cutoff (PowerWordContent.powerBound D cutoff L)
  ΛP ΛR hP hR).wt ((0, 0) : Sector I)

/-- **The right vacuum entries at negative height.** The vacuum entries of the closed diagrams of
`SKM.smul_bubRs_eq_cl_of_neg` and of the odd bubble at negative vacuum height, at the vacuum
weight of the probe reservoir with probe exponents `m` and reservoir levels `cutoff`, when the
probe cutoff of the colour is positive. Intermediate hypothesis. -/
structure VacuumRightNegativeEntries : Prop where
  neg_even : ∀ i, D.parity i = 0 → 0 < probeCutoff D m i → D.h i ν₀ < 0 → ∀ s : ℕ,
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR hF ν₀
      (SKM.etaL i ((s : ℤ) - D.h i ν₀ - 1).toNat ++ SKM.dcapL i (-D.h i ν₀ - 1).toNat)
      ((SKM.sChain_etaL i _).append (SKM.sChain_dcapL i _))
      (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)))
  neg_odd : ∀ i, D.parity i = 1 → 0 < probeCutoff D m i → D.h i ν₀ < 0 → ∀ s : ℕ,
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR hF ν₀
      (SKM.etaL i (((2 * s : ℕ) : ℤ) - D.h i ν₀ - 1).toNat ++ SKM.dcapL i (-D.h i ν₀ - 1).toNat)
      ((SKM.sChain_etaL i _).append (SKM.sChain_dcapL i _))
      (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i)))
  odd_neg : ∀ i : {i : I // D.parity i = 1}, 0 < probeCutoff D m i.1 → D.h i.1 ν₀ < 0 →
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR hF ν₀
      (SKM.etaL i.1 (((1 : ℕ) : ℤ) - D.h i.1 ν₀ - 1).toNat ++
        SKM.dcapL i.1 (-D.h i.1 ν₀ - 1).toNat)
      ((SKM.sChain_etaL i.1 _).append (SKM.sChain_dcapL i.1 _))
      (SKM.SYM.probeSign D k cutoff i • SKM.SYM.delta D k i)

include hF in
/-- **The right vacuum entries at nonpositive height** at the vacuum weight `ΛP - ΛR` of the
probe reservoir, from the entries at negative height, for positive probe cutoffs and reservoir
levels. The entries at zero height are `vacuumEntry_zero_even`, `vacuumEntry_zero_odd` and
`vacuumEntry_odd_zero`. -/
theorem vacuumRightEntries_of_negative
    (hneg : VacuumRightNegativeEntries D Sc m cutoff ΛP ΛR L hP hR hF)
    (hPc : ∀ i, 0 < probeCutoff D m i) (hN : ∀ i, 0 < cutoff i) (μ : X) (hμ : ΛP - ΛR = μ) :
    VacuumRightEntries D Sc m cutoff ΛP ΛR L hP hR hF μ m cutoff := by
  have hw := (tensorVacuumWeight D Sc m cutoff ΛP ΛR L hP hR).trans hμ
  subst hw
  exact ⟨fun i hi h s => hneg.neg_even i hi (hPc i) h s,
    fun i hi h s => vacuumEntry_zero_even D Sc m cutoff ΛP ΛR L hP hR hF i hi (hN i) h s,
    fun i hi h s => hneg.neg_odd i hi (hPc i) h s,
    fun i hi h s => vacuumEntry_zero_odd D Sc m cutoff ΛP ΛR L hP hR hF i hi (hN i) h s,
    fun i h => hneg.odd_neg i (hPc i.1) h,
    fun i h => vacuumEntry_odd_zero D Sc m cutoff ΛP ΛR L hP hR hF i.1 i.2 (hN i.1) h⟩

end SwappedAssembly.SupportedSectors

/-- **The right vacuum entries of the probe reservoirs** from their entries at negative height.
The negative-height families are proved (`SupportedSectors.vacuumRightNegativeEntries`), which
gives `rightVacuumEntrySupply`. -/
theorem rightVacuumEntrySupply_of_negative
    (h : ∀ {J Y k : Type u} [AddCommGroup Y] [CommRing k] [Fintype J]
      (E : SKM.Datum J Y) (Sc : SKM.Scalars E k) (m cutoff : J → ℕ) (ΛP ΛR : Y)
      (L : J × ℕ → ℕ) (hP : ∀ i, (probeCutoff E m i : ℤ) = E.h i ΛP)
      (hR : ∀ i, (cutoff i : ℤ) = E.h i ΛR)
      (hF : SwappedAssembly.SupportedSectors.ProbeActionInputs E Sc m cutoff
        (ELVOld.PowerWordContent.powerBound E cutoff L) ΛP ΛR hP hR),
      SwappedAssembly.SupportedSectors.VacuumRightNegativeEntries E Sc m cutoff ΛP ΛR L hP hR
        hF) :
    RightVacuumEntrySupply.{u} := by
  intro J Y k _ _ _ E Sc m cutoff ΛP ΛR L hP hR hF hPc hN
  exact SwappedAssembly.SupportedSectors.vacuumRightEntries_of_negative E Sc m cutoff ΛP ΛR L hP hR
      hF (h E Sc m cutoff ΛP ΛR L hP hR hF) hPc hN _ rfl

end OddMath.QuiverHecke
