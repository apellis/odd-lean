import OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExpansion
import NonVacuity.RouquierHomMixedRational
import Lean.Util.CollectAxioms
noncomputable section
open OddMath.SKM OddMath.QuiverHecke.SwappedAssembly
open NonVacuity.RouquierHomMixedRational
open scoped BigOperators
namespace CrossCoeffExpansionConsumer
private abbrev π : S × S →+* S := RingHom.fst S S
private def evenX : S × S := (1, 0)
private def reservoirPair : S × S := (reservoir, 1)
private def evenA : S × S := (-Ring.inverse ((1 : S) - reservoir), 1)
private theorem even_inverse : evenA * (reservoirPair - evenX) = 1 := by
  apply Prod.ext
  · change -Ring.inverse ((1 : S) - reservoir) * (reservoir - 1) = 1
    rw [← neg_sub (1 : S) reservoir, neg_mul_neg]
    exact Ring.inverse_mul_cancel _
      (mixedEvenDenominator_isUnit (1 : Sˣ) reservoir (Commute.one_left _) 3 reservoir_cube)
  · change (1 : S) * (1 - 0) = 1
    simp only [sub_zero, one_mul]
private theorem even_exchange : Commute evenX reservoirPair := by
  change evenX * reservoirPair = reservoirPair * evenX
  apply Prod.ext <;> simp [evenX, reservoirPair]

example : π evenA = -∑ r ∈ Finset.range 3,
    Ring.inverse (π evenX) ^ (r + 1) * π reservoirPair ^ r :=
  mixedCoefficient_even_map_expansion π evenX reservoirPair evenA
    (show IsUnit (1 : S) from isUnit_one) even_exchange even_inverse 3 reservoir_cube

private def oddX : S × S := (probe, 0)
private def oddA : S × S := ((probe - reservoir) * Ring.inverse (probe ^ 2 - reservoir ^ 2), 1)
private theorem odd_exchange : oddX * reservoirPair = -(reservoirPair * oddX) := by
  apply Prod.ext
  · exact exchange
  · change (0 : S) * 1 = -(1 * 0)
    simp only [zero_mul, mul_zero, neg_zero]
private theorem odd_inverse : oddA * (oddX ^ 2 - reservoirPair ^ 2) = oddX - reservoirPair := by
  apply Prod.ext
  · change ((probe - reservoir) * Ring.inverse (probe ^ 2 - reservoir ^ 2)) *
      (probe ^ 2 - reservoir ^ 2) = probe - reservoir
    have hu : IsUnit (probe ^ 2 - reservoir ^ 2) :=
      mixedOddDenominator_isUnit probeUnit reservoir exchange 3 reservoir_cube
    rw [mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one]
  · change (1 : S) * (0 ^ 2 - 1 ^ 2) = 0 - 1
    simp only [zero_pow (by decide : 2 ≠ 0), one_pow, one_mul]

example : π oddA = ∑ r ∈ Finset.range 6,
    (-1 : S) ^ r * Ring.inverse (π oddX) ^ (r + 1) * π reservoirPair ^ r :=
  mixedCoefficient_odd_map_expansion π oddX reservoirPair oddA
    probeUnit.isUnit odd_exchange odd_inverse 3 reservoir_cube

/-- The specified component bound is not a bound for the source operator. -/
example (n : ℕ) : reservoirPair ^ n ≠ 0 := by
  intro h
  have hs := congrArg Prod.snd h
  change (1 : S) ^ n = 0 at hs
  have hs' : (1 : S) = 0 := by simpa only [one_pow] using hs
  have hk : (1 : K) = 0 := congrArg (fun z : S => z 0 0 0 0) hs'
  exact (by decide : (1 : K) ≠ 0) hk

example : π reservoirPair ^ 2 ≠ 0 := reservoir_square_ne
example : (2 : K) * 5 = 1 := by decide
example : (3 : K) ≠ 0 ∧ (3 : K) * 3 = 0 := by decide

/-- The evaluated even diagonal has the required negative constant term. -/
example : (π evenA) 0 0 0 0 = -1 := by
  have h := mixedCoefficient_even_map_expansion π evenX reservoirPair evenA
    (show IsUnit (1 : S) from isUnit_one) even_exchange even_inverse 3 reservoir_cube
  rw [h]
  change (-(∑ r ∈ Finset.range 3, Ring.inverse (1 : S) ^ (r + 1) * reservoir ^ r)) 0 0 0 0 = -1
  simp only [Ring.inverse_one, one_pow, one_mul]
  decide
end CrossCoeffExpansionConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExpansion
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"
