import OddMath.Algebra.DegreeShiftRowDivision
import Lean.Util.CollectAxioms

noncomputable section
namespace DegreeShiftRowConsumer
open OddMath.Algebra

def shiftTwo : (ℕ →₀ ℤ) →ₗ[ℤ] (ℕ →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun n => n + 2)

theorem aboveTwo (d n : ℕ) (b : ℤ) (h : d + 2 < n + 0) :
    shiftTwo (Finsupp.single d b) n = 0 := by
  simp only [shiftTwo, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  exact Finsupp.single_eq_of_ne (by omega)

theorem topTwo (d n : ℕ) (b : ℤ) (h : n + 0 = d + 2) :
    shiftTwo (Finsupp.single d b) n = (LinearEquiv.refl ℤ ℤ) b := by
  simp only [shiftTwo, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  have hn : n = d + 2 := by omega
  rw [hn, Finsupp.single_eq_same]
  rfl

def divisionTwo :
    (DegreeShiftRow.high (k := ℤ) (M := ℤ) 0 2 ×
      DegreeShiftRow.window (k := ℤ) (M := ℤ) 0 2) ≃ₗ[ℤ] (ℕ →₀ ℤ) :=
  DegreeShiftRow.divisionEquiv shiftTwo (fun _ => LinearEquiv.refl ℤ ℤ)
    0 2 aboveTwo topTwo

example (f : ℕ →₀ ℤ) : divisionTwo (divisionTwo.symm f) = f :=
  divisionTwo.apply_symm_apply f

example (x : DegreeShiftRow.high (k := ℤ) (M := ℤ) 0 2 ×
    DegreeShiftRow.window (k := ℤ) (M := ℤ) 0 2) : divisionTwo.symm (divisionTwo x) = x :=
  divisionTwo.symm_apply_apply x

example : Function.Injective shiftTwo :=
  DegreeShiftRow.injective shiftTwo (fun _ => LinearEquiv.refl ℤ ℤ) 0 2 aboveTwo topTwo (by decide)

example : shiftTwo (Finsupp.single 1 7) 3 = 7 := by
  exact topTwo 1 3 7 rfl
end DegreeShiftRowConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.Algebra.DegreeShiftRowDivision
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"
