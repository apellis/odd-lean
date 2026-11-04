import OddMath.QuiverHecke.SwappedVacuumParameters
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke
open SwappedVacuumParameters
namespace NonVacuity.SwappedVacuumParameters

/-- Connected mixed colours and an independent common coroot-kernel coordinate. -/
private def D : SKM.Datum Bool ((Bool → ℤ) × ℤ) where
  cd :=
    { root := fun j => (fun i => if i = j then 2 else -2, 0)
      coroot := fun i => (LinearMap.proj i).comp (LinearMap.fst ℤ (Bool → ℤ) ℤ)
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun i => if i then 1 else 0
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else -2)
    split_ifs <;> norm_num

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => (by norm_num : (2 : ℚ) ≠ 0).isUnit

private def μ : (Bool → ℤ) × ℤ := (fun i => if i then -5 else 3, 7)
private def s : List Bool := [false, true, false]

example : D.d false true = 2 ∧ D.parity false = 0 ∧ D.parity true = 1 := by
  norm_num [D, SKM.Datum.d, SKM.Datum.h, SKM.Datum.α]

/-- Both parity conventions are tested at a repeated-colour observation. -/
example : probeExponent D μ s 2 false = 24 ∧ probeExponent D μ s 2 true = 9 ∧
    reservoirLevel D μ s 2 false = 21 ∧ reservoirLevel D μ s 2 true = 23 := by
  norm_num [probeExponent, probeLevel, reservoirLevel, vacuumCutoff, D, μ, s, SKM.Datum.h]

example (i : Bool) :
    (probeCutoff (ReservoirWeights.pairingExtension D) (probeExponent D μ s 2) i : ℤ) =
      (ReservoirWeights.pairingExtension D).h i (probeWeight D μ s 2) :=
  probe_pairing D μ s 2 i

example (i : Bool) :
    (reservoirLevel D μ s 2 i : ℤ) =
      (ReservoirWeights.pairingExtension D).h i (reservoirWeight D μ s 2) :=
  reservoir_pairing D μ s 2 i

/-- The external weight is retained literally, not just its coroot values. -/
example : (probeWeight D μ s 2 - reservoirWeight D μ s 2).1.2 = 7 := by
  rw [weight_difference]
  rfl

example : probeWeight D μ s 2 - reservoirWeight D μ s 2 ≠ 0 := by
  intro h
  have hh := congrArg (fun z => z.1.2) h
  rw [weight_difference] at hh
  norm_num [μ] at hh

example (i : Bool) : 0 < probeExponent D μ s 2 i := probeExponent_pos D μ s 2 i

example (i : Bool) :
    2 + 2 * s.length.choose 2 <
        probeCutoff (ReservoirWeights.pairingExtension D) (probeExponent D μ s 2) i ∧
      2 + 2 * s.length.choose 2 < reservoirLevel D μ s 2 i :=
  cutoff_bounds D μ s 2 i

example (j : Bool × ℕ) : 0 < coefficientPower s 2 j := coefficientPower_pos s 2 j

/-- The chosen powers discharge the actual half-turn coordinate bound; no bound is assumed. -/
example : Function.Injective (fun x : ExtendedAtMost D Sc s s 2 =>
    powerWordHalfTurnCoordinate D Sc (reservoirLevel D μ s 2)
      (coefficientPower s 2) s s x.val) :=
  powerWordHalfTurnCoordinate_reservoir_injective D Sc (coefficientPower s 2) μ s s 2
    (coefficientPower_weight D s 2)

end NonVacuity.SwappedVacuumParameters

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedVacuumParameters
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
