/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteSwappedRightField
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumRightEntriesOdd
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumRightEntriesEven

/-! # The right vacuum entries at negative height and the conjecture

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, in the research scope of `FieldScopeBoundary.md`; (2.11), (2.13),
(2.17), (2.18), and `InverseColumnMoments.md`.

The fields of `VacuumRightNegativeEntries` are `vacuumEntry_neg_even`, `vacuumEntry_neg_odd`
and `vacuumEntry_odd_neg`:

* `SupportedSectors.vacuumRightNegativeEntries`: the right vacuum entries at negative height of
  every probe reservoir;
* `rightVacuumEntrySupply`: `RightVacuumEntrySupply`;
* `swappedRightEntriesField`: `SwappedRightEntriesField`;
* `nondegeneracy_of_symmetrizer`: the Nondegeneracy Conjecture for a symmetrizable Cartan
  superdatum and homogeneous parameters over a commutative ring in which `2` is invertible.
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

/-- **The right vacuum entries at negative height** of one probe reservoir. -/
theorem vacuumRightNegativeEntries :
    VacuumRightNegativeEntries D Sc m cutoff ΛP ΛR L hP hR hF :=
  ⟨fun i hi hP0 hh s => vacuumEntry_neg_even D Sc m cutoff ΛP ΛR L hP hR hF i hi hP0 hh s,
    fun i hi hP0 hh s => vacuumEntry_neg_odd D Sc m cutoff ΛP ΛR L hP hR hF i hi hP0 hh s,
    fun i hP0 hh => vacuumEntry_odd_neg D Sc m cutoff ΛP ΛR L hP hR hF cutoff i hP0 hh rfl⟩

end SwappedAssembly.SupportedSectors

/-- **The right vacuum entries of the probe reservoirs.** -/
theorem rightVacuumEntrySupply : RightVacuumEntrySupply.{u} := by
  apply rightVacuumEntrySupply_of_negative
  intro J Y k _ _ _ E Sc m cutoff ΛP ΛR L hP hR hF
  exact SwappedAssembly.SupportedSectors.vacuumRightNegativeEntries E Sc m cutoff ΛP ΛR
    L hP hR hF

variable {I X : Type u} [AddCommGroup X] {D : SKM.Datum I X}

/-- **The right vacuum entries at every route index.** -/
theorem swappedRightEntriesField (D : SKM.Datum I X) : SwappedRightEntriesField D :=
  swappedRightEntriesField_of_supply rightVacuumEntrySupply

/-- **The Nondegeneracy Conjecture** (Brundan–Ellis, arXiv:1701.04133v2, §8) for a
symmetrizable Cartan superdatum and homogeneous parameters over a commutative ring in which `2`
is invertible. -/
theorem nondegeneracy_of_symmetrizer (sy : SKM.Symmetrizer D) {R : Type w} [CommRing R]
    (h₂ : IsUnit (2 : R)) {Sc : SKM.Scalars D R} (hh : Sc.Homogeneous) (cs : SKM.CScalars Sc) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_rightVacuumEntrySupply rightVacuumEntrySupply sy h₂ hh cs

end OddMath.QuiverHecke
