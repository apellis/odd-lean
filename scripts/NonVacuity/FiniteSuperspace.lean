import OddMath.Algebra.FiniteSuperspace
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.FiniteSuperspace
namespace FiniteSuperspaceConsumer
def P : SVec ℤ := SVec.ofProd ℤ ℤ
def V : Bool → SVec ℤ := fun _ => P
def sample : product V := fun b => if b then (0, 1) else (0, 2)

example : sample ∈ (product V).part 1 := by
  rw [mem_product_part]
  intro b
  cases b
  · exact SVec.ofProd_mem_part_one 2
  · exact SVec.ofProd_mem_part_one 1

example : assembleColumns V P (fun _ => 𝟙 P) sample = (0, 3) := by
  change ((0, 2) : ℤ × ℤ) + (0, 1) = (0, 3)
  rfl

example : assembleColumns V P (fun _ => 𝟙 P) ∈ SVec.parityHom (product V) P 0 :=
  assembleColumns_even V P (fun _ => 𝟙 P) (fun _ => id_mem P)

example : assembleRows P V (fun _ => 𝟙 P) ∈ SVec.parityHom P (product V) 0 :=
  assembleRows_even P V (fun _ => 𝟙 P) (fun _ => id_mem P)

example (b : Bool) : assembleRows P V (fun _ => 𝟙 P) (1, 2) b = (1, 2) := rfl
example : sample false ≠ 0 := by
  change ((0, 2) : ℤ × ℤ) ≠ (0, 0)
  norm_num
end FiniteSuperspaceConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.Algebra.FiniteSuperspace
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations including private/generated"

