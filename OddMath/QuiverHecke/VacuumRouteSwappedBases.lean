/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteFields
import OddMath.QuiverHecke.SwappedVacuumParameters
import OddMath.QuiverHecke.SwappedAssembly.SupportedAction
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorMatrixCoefficients

/-! # Route bases from the swapped probe-reservoir action

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, in the research scope of `FieldScopeBoundary.md`.

`swappedRouteBases : VacuumRouteBases D` chooses at
every route index `ι` the base given by the swapped action on the probe-reservoir
product (`SwappedAssembly.SupportedSectors.pointwiseUpwardModuleAction`):

* the datum is the pairing extension of the restriction of `D` to `ι.J`, with the
  restricted scalars, and the supported-action inputs are those carried by the index;
* the probe and reservoir highest weights are `SwappedVacuumParameters.probeWeight`
  and `reservoirWeight`, with exponents `probeExponent` and levels `reservoirLevel`
  of the vacuum schedule, and the tensor source and target families with the
  coefficient powers `SwappedVacuumParameters.coefficientPower`;
* the vacuum is the tensor matrix vacuum of the source word, transported along
  `probeWeight - reservoirWeight = (μ, 0)`;
* the raw coefficient action is the coefficient action on the tensor matrix module.

With these bases fixed, the four route fields of `VacuumRouteFields` become statements
about the swapped action.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u

section Schedule
variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X)

/-- The probe exponent of the pairing extension at `(μ, 0)` is that of `D` at `μ`. -/
theorem probeExponent_pairingExtension (μ : X) (t : List I) (d : ℕ) :
    probeExponent (ReservoirWeights.pairingExtension D) (μ, 0) t d = probeExponent D μ t d := by
  funext i
  simp only [probeExponent, probeLevel, ReservoirWeights.pairingExtension_parity,
    ReservoirWeights.pairingExtension_h, Pi.zero_apply, add_zero]

/-- The reservoir level of the pairing extension at `(μ, 0)` is that of `D` at `μ`. -/
theorem reservoirLevel_pairingExtension (μ : X) (t : List I) (d : ℕ) :
    reservoirLevel (ReservoirWeights.pairingExtension D) (μ, 0) t d =
      reservoirLevel D μ t d := by
  funext i
  simp only [reservoirLevel, ReservoirWeights.pairingExtension_h, Pi.zero_apply, add_zero]

end Schedule

variable {I X : Type u} [AddCommGroup X] {D : SKM.Datum I X}

namespace VacuumRouteIndex
variable (ι : VacuumRouteIndex D)

/-- The probe exponents of the sector. -/
abbrev exponent : ι.J → ℕ := probeExponent ι.datum ι.weight ι.t ι.d

/-- The reservoir levels of the sector. -/
abbrev level : ι.J → ℕ := reservoirLevel ι.datum ι.weight ι.t ι.d

/-- The probe highest weight of the sector. -/
abbrev probeHW : X × (ι.J → ℤ) :=
  SwappedVacuumParameters.probeWeight (D.restrictColours ι.J) ι.μ ι.t ι.d

/-- The reservoir highest weight of the sector. -/
abbrev reservoirHW : X × (ι.J → ℤ) :=
  SwappedVacuumParameters.reservoirWeight (D.restrictColours ι.J) ι.μ ι.t ι.d

/-- The coefficient powers of the tensor families. -/
abbrev power : ι.J × ℕ → ℕ := SwappedVacuumParameters.coefficientPower ι.t ι.d

/-- The degree bound of the tensor families. -/
abbrev bound : ℕ := ELVOld.PowerWordContent.powerBound ι.datum ι.level ι.power

theorem probe_pairing (i : ι.J) :
    (probeCutoff ι.datum ι.exponent i : ℤ) = ι.datum.h i ι.probeHW :=
  (congrArg (fun m => (probeCutoff ι.datum m i : ℤ))
    (probeExponent_pairingExtension (D.restrictColours ι.J) ι.μ ι.t ι.d)).trans
    (SwappedVacuumParameters.probe_pairing (D.restrictColours ι.J) ι.μ ι.t ι.d i)

theorem reservoir_pairing (i : ι.J) : (ι.level i : ℤ) = ι.datum.h i ι.reservoirHW :=
  (congrArg (fun m : ι.J → ℕ => (m i : ℤ))
    (reservoirLevel_pairingExtension (D.restrictColours ι.J) ι.μ ι.t ι.d)).trans
    (SwappedVacuumParameters.reservoir_pairing (D.restrictColours ι.J) ι.μ ι.t ι.d i)

theorem weight_difference : ι.probeHW - ι.reservoirHW = ι.weight :=
  SwappedVacuumParameters.weight_difference (D.restrictColours ι.J) ι.μ ι.t ι.d

/-- The inputs of the supported action of the sector, carried by the index. -/
theorem actionInputs :
    SwappedAssembly.SupportedSectors.ProbeActionInputs ι.datum ι.scalars ι.exponent ι.level
      ι.bound ι.probeHW ι.reservoirHW ι.probe_pairing ι.reservoir_pairing :=
  ι.inputs ι.exponent ι.level ι.bound ι.probeHW ι.reservoirHW ι.probe_pairing
    ι.reservoir_pairing

/-- The swapped action on the probe-reservoir product of the sector, at weight `w`,
with the tensor source and target families. -/
def actionAt (w : X × (ι.J → ℤ)) :
    UpwardModuleAction.{u, u + 1} ι.datum ι.scalars w :=
  SwappedAssembly.SupportedSectors.pointwiseUpwardModuleAction ι.datum ι.scalars ι.exponent
    ι.level ι.bound ι.probeHW ι.reservoirHW ι.probe_pairing ι.reservoir_pairing
    (ι.actionInputs).dot (ι.actionInputs).window
    (SwappedAssembly.SupportedSectors.tensorSourceFamily ι.datum ι.scalars ι.exponent ι.level
      ι.probeHW ι.reservoirHW ι.power ι.t)
    (SwappedAssembly.SupportedSectors.tensorTargetFamily ι.datum ι.scalars ι.exponent ι.level
      ι.probeHW ι.reservoirHW ι.power) w

/-- The swapped action of the sector, at its weight `(μ, 0)`. -/
def swappedAction :
    UpwardModuleAction.{u, u + 1} ι.datum ι.scalars ι.weight :=
  ι.actionAt ι.weight

/-- The vacuum of the sector: the tensor matrix vacuum of the source word,
transported along `probeHW - reservoirHW = (μ, 0)`. -/
def swappedVacuum : (ι.swappedAction).V ι.t :=
  cast (congrArg (fun w => (ι.actionAt w).V ι.t) ι.weight_difference)
    (SwappedAssembly.SupportedSectors.tensorMatrixVacuum ι.datum ι.scalars ι.exponent ι.level
      ι.probeHW ι.reservoirHW ι.power ι.t)

/-- The base of the sector: the swapped action, its vacuum, and the raw coefficient
action on the tensor matrix module. -/
def swappedBase : VacuumRouteBase ι.datum ι.scalars ι.weight ι.t where
  A := ι.swappedAction
  vacuum := ι.swappedVacuum
  raw := SwappedAssembly.SupportedSectors.tensorMatrixCoefficientAction ι.datum ι.scalars
    ι.exponent ι.level ι.probeHW ι.reservoirHW ι.power ι.t
    (SKM.ob ι.datum ι.weight (upWord ι.t))

end VacuumRouteIndex

/-- **The swapped route bases**: at every route index, the swapped action on the
probe-reservoir product of the sector, with the tensor matrix vacuum and the raw
coefficient action. -/
def swappedRouteBases (D : SKM.Datum I X) : VacuumRouteBases D := fun ι =>
  ι.swappedBase

@[simp] theorem swappedRouteBases_A (ι : VacuumRouteIndex D) :
    (swappedRouteBases D ι).A = ι.swappedAction := rfl

@[simp] theorem swappedRouteBases_vacuum (ι : VacuumRouteIndex D) :
    (swappedRouteBases D ι).vacuum = ι.swappedVacuum := rfl

end OddMath.QuiverHecke
