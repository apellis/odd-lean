import OddMath.QuiverHecke.SwappedVacuumRecovery
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

/-- Vacuum evaluations at every degree for one two-colour pair give upward
coefficient injectivity; this is a conditional consumer of the interface. -/
example (μ : Bool → ℤ)
    (h : ∀ d, Nonempty (SwappedVacuumEvaluation oddDatum params bubbles μ
      [false, true] [true, false] d)) :
    Function.Injective (upwardCoefficientMap oddDatum params bubbles μ
      [false, true] [true, false]) :=
  upwardCoefficientMap_injective_of_vacuum_evaluations μ _ _ h

/-- The conditional field theorem at a two-odd-colour datum over `ℚ`. -/
example (h : ∀ (t t' : List Bool), wt oddDatum 0 (ups t) = wt oddDatum 0 (ups t') →
      ∀ (μ : Bool → ℤ) (d : ℕ),
        Nonempty (SwappedVacuumEvaluation oddDatum params bubbles μ t t' d)) :
    NondegeneracyConjecture bubbles :=
  nondegeneracy_of_vacuum_evaluations h

#print axioms SwappedVacuumEvaluation.toBoundedCyclicRecovery
#print axioms upwardCoefficientMap_injective_of_vacuum_evaluations
#print axioms nondegeneracy_of_vacuum_evaluations

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.SwappedVacuumRecovery then
      for name in env.header.moduleData[i]!.constNames do
        for axiomName in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations found"
  logInfo m!"Audited {count} owned declarations: standard axioms only"
