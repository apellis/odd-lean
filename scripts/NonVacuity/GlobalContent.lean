import OddMath.QuiverHecke.CyclotomicAction.Global
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if #[`OddMath.QuiverHecke.CyclotomicAction.Global].contains env.header.moduleNames[i]! then
      for n in env.header.moduleData[i]!.constNames do
        for a in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Disallowed {a} in {n}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} declarations"
namespace Test
open OddMath.QuiverHecke.CyclotomicAction
def D : OddMath.SKM.Datum Bool (Bool → ℤ) where
  cd := { root := fun j i => if i = j then 2 else 0
          coroot := fun i => LinearMap.proj i
          coroot_root_self := fun i => by simp }
  isGCM := { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
             offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
             zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else 0)
    split <;> simp
example : ¬ ∃ w : ℕ → (Bool → ℤ), ∀ β, blockWeight D 0 β = w β.card := by
  apply blockWeight_not_card D 0 false true
  intro e
  have h := congrFun e false
  norm_num [D, OddMath.SKM.Datum.α] at h
example : IsEmpty {γ : WeightBlocks D 0 (-(D.α false)) //
    blockSucc D 0 false (neg_add_cancel _) γ = ⟨0, by simp⟩} :=
  isEmpty_of_not_mem D 0 false (neg_add_cancel _) ⟨0, by simp⟩ (by simp)
end Test
