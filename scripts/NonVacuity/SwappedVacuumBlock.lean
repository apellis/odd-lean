import OddMath.QuiverHecke.SwappedVacuumBlock
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

/-- The schedule at an odd colour with `h = -3`, one-letter word and `d = 2`:
`N₀ = 3`, `P = 6`, `N = 9`, probe exponent `3`, and `P - N = h`. -/
example : vacuumCutoff [false] 2 = 3 ∧
    probeLevel oddDatum (fun _ => -3) [false] 2 false = 6 ∧
    reservoirLevel oddDatum (fun _ => -3) [false] 2 false = 9 ∧
    probeExponent oddDatum (fun _ => -3) [false] 2 false = 3 := by
  have hh : oddDatum.h false (fun _ => -3) = -3 := rfl
  have hp : oddDatum.parity false = 1 := rfl
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp [probeLevel, reservoirLevel, probeExponent, vacuumCutoff, hh]
  simp [hp]

example : ((probeLevel oddDatum (fun _ => -3) [false] 2 false : ℤ) -
    reservoirLevel oddDatum (fun _ => -3) [false] 2 false) = oddDatum.h false (fun _ => -3) :=
  probeLevel_sub_reservoirLevel _ _ _ _ _

/-- The schedule substitution preserves the coefficient weight. -/
example (μ : Bool → ℤ) (t : List Bool) (d : ℕ) :
    PreservesCoefficientWeight oddDatum (vacuumSubstitution oddDatum ℚ μ t d).toLinearMap :=
  vacuumSubstitution_weight oddDatum ℚ μ t d

/-- A vacuum block is a vacuum evaluation. -/
example (μ : Bool → ℤ) (d : ℕ)
    (B : SwappedVacuumBlock oddDatum params bubbles μ [false, true] [true, false] d) :
    SwappedVacuumEvaluation oddDatum params bubbles μ [false, true] [true, false] d :=
  B.toSwappedVacuumEvaluation

/-- The conditional field theorem from vacuum blocks at a two-odd-colour datum over `ℚ`. -/
example (h : ∀ (t t' : List Bool), wt oddDatum 0 (ups t) = wt oddDatum 0 (ups t') →
      ∀ (μ : Bool → ℤ) (d : ℕ),
        Nonempty (SwappedVacuumBlock oddDatum params bubbles μ t t' d)) :
    NondegeneracyConjecture bubbles :=
  nondegeneracy_of_vacuum_blocks oddDatum params bubbles h

#print axioms SwappedVacuumBlock.toSwappedVacuumEvaluation
#print axioms nondegeneracy_of_vacuum_blocks

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.SwappedVacuumBlock then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"
