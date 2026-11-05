import OddMath.QuiverHecke.SwappedVacuumBlock
import OddMath.QuiverHecke.ReservoirWeightParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCoefficients

/-! # Explicit weights and cutoffs for a swapped vacuum observation

`SwappedNondegeneracy.md` §2 and `SwappedVacuumCoordinates.md` §§6–7 choose
the observation window before constructing the factors. This module joins
that schedule to the literal probe cutoff and constructs the two highest
weights in the pairing extension. Their difference retains the original
weight, including its common coroot kernel. The constant coefficient-power
exponent satisfies the lower bound needed by the half-turn coordinates;
the upper coefficient bound for the resulting power module is supplied
separately by `ELVOld.PowerWordContent.powerBound`.
-/
noncomputable section
namespace OddMath.QuiverHecke
universe u
variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X)

namespace SwappedVacuumParameters

/-- The explicit probe highest weight `(0,P)` in the pairing extension. -/
def probeWeight (μ : X) (s : List I) (d : ℕ) : X × (I → ℤ) :=
  (0, fun i => (probeLevel D μ s d i : ℤ))

/-- The explicit reservoir highest weight `(-μ,P)`, with the same second coordinate. -/
def reservoirWeight (μ : X) (s : List I) (d : ℕ) : X × (I → ℤ) :=
  (-μ, fun i => (probeLevel D μ s d i : ℤ))

theorem weight_difference (μ : X) (s : List I) (d : ℕ) :
    probeWeight D μ s d - reservoirWeight D μ s d = (μ, 0) := by
  simp [probeWeight, reservoirWeight]

/-- The prescribed exponent gives exactly the scheduled probe level in both parities. -/
theorem probeCutoff_eq (μ : X) (s : List I) (d : ℕ) (i : I) :
    probeCutoff (ReservoirWeights.pairingExtension D) (probeExponent D μ s d) i =
      probeLevel D μ s d i := by
  unfold probeCutoff probeDotExponent probeExponent
  simp only [ReservoirWeights.pairingExtension_parity]
  split_ifs
  · unfold probeLevel
    omega
  · simp

/-- The actual probe factor's required highest-weight equation. -/
theorem probe_pairing (μ : X) (s : List I) (d : ℕ) (i : I) :
    (probeCutoff (ReservoirWeights.pairingExtension D) (probeExponent D μ s d) i : ℤ) =
      (ReservoirWeights.pairingExtension D).h i (probeWeight D μ s d) := by
  rw [probeCutoff_eq]
  simp [probeWeight, SKM.Datum.h]

/-- The actual reservoir factor's required highest-weight equation. -/
theorem reservoir_pairing (μ : X) (s : List I) (d : ℕ) (i : I) :
    (reservoirLevel D μ s d i : ℤ) =
      (ReservoirWeights.pairingExtension D).h i (reservoirWeight D μ s d) := by
  have h := probeLevel_sub_reservoirLevel D μ s d i
  simp only [ReservoirWeights.pairingExtension_h, reservoirWeight]
  change _ = D.cd.coroot i (-μ) + _
  rw [map_neg]
  change _ = -D.h i μ + _
  omega

/-- A single strict lower bound works simultaneously for both factors. -/
theorem cutoff_bounds (μ : X) (s : List I) (d : ℕ) (i : I) :
    d + 2 * s.length.choose 2 <
        probeCutoff (ReservoirWeights.pairingExtension D) (probeExponent D μ s d) i ∧
      d + 2 * s.length.choose 2 < reservoirLevel D μ s d i := by
  rw [probeCutoff_eq]
  unfold probeLevel reservoirLevel vacuumCutoff
  omega

/-- The constant positive exponent chosen in §2 for every elementary coefficient. -/
def coefficientPower (s : List I) (d : ℕ) : I × ℕ → ℕ :=
  fun _ => vacuumCutoff s d

/-- Every chosen elementary power has at least the required coefficient weight. -/
theorem coefficientPower_weight (s : List I) (d : ℕ) (j : I × ℕ) :
    vacuumCutoff s d ≤ coefficientPower s d j * SKM.SYM.elementaryWeight D j := by
  have hj : 1 ≤ SKM.SYM.elementaryWeight D j := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  simpa only [coefficientPower, Nat.mul_one] using Nat.mul_le_mul_left (vacuumCutoff s d) hj

end SwappedVacuumParameters
end OddMath.QuiverHecke
