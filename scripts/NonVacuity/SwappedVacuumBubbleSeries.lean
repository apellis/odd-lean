import OddMath.QuiverHecke.SwappedVacuumBubbleSeries
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke OddMath.SKM
open scoped Classical

private def oddDatum : Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else 0
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else 0)
    split <;> simp

private def params : Scalars oddDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)

private def bubbles : CScalars params where
  c := fun _ _ => 1
  shift := fun _ _ _ => by simp [params]

/-- Uniqueness of left inverses on a concrete series: `K = 1 - z`, `x = Σ zⁿ`,
`y = Σ 1ⁿ zⁿ`. -/
example (n : ℕ) : (1 : ℚ) = 1 ^ n :=
  eq_of_sum_mul_eq_zero (K := fun s => if s = 0 then (1 : ℚ) else if s = 1 then -1 else 0)
    (x := fun _ => 1) (y := fun m => 1 ^ m) (by simp) rfl (pow_zero _)
    (fun m hm => by
      obtain ⟨m, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      rw [Finset.sum_range_succ', Finset.sum_range_succ']; simp [Finset.sum_eq_zero])
    (fun m hm => by
      obtain ⟨m, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      rw [Finset.sum_range_succ', Finset.sum_range_succ']; simp [Finset.sum_eq_zero]) n

/-- The substituted series and the moment series are inverse, at the vacuum
probe exponents of the odd datum. -/
example (μ : Bool → ℤ) (t : List Bool) (d : ℕ) (i : Bool) :
    VacuumSeries.substitutedSeries ℚ (SYM.probeSeries oddDatum ℚ (probeExponent oddDatum μ t d)) i *
      VacuumSeries.momentSeries ℚ (SYM.probeSeriesInv oddDatum ℚ (probeExponent oddDatum μ t d)) i
        = 1 :=
  VacuumSeries.substitutedSeries_mul_momentSeries ℚ (SYM.probeSeries_mul_inv oddDatum ℚ _) i

/-- (A16) at the vacuum schedule from the moment hypothesis, at the odd datum. -/
example (μ : Bool → ℤ) (t : List Bool) (d : ℕ) (A : UpwardModuleAction oddDatum params μ)
    (raw : SYM oddDatum ℚ →ₐ[ℚ] Module.End ℚ (A.V t))
    (h : VacuumMoments bubbles A t raw (probeExponent oddDatum μ t d)
      (reservoirLevel oddDatum μ t d)) (a : SYM oddDatum ℚ) :
    A.bubbles bubbles t a = raw (vacuumSubstitution oddDatum ℚ μ t d a) :=
  h.vacuum_bubbles_eq a

#print axioms VacuumMoments.bubbles_eq

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.SwappedVacuumBubbleSeries then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"
