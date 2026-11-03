import OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairQuadratic
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable
import Lean.Util.CollectAxioms

noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVWeightPairQuadraticExamples

private def D : SKM.Datum Bool (Bool → ℤ) :=
  { AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => AsymmetricParameters.datum.even_of_odd i j rfl }
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private abbrev X := Bool → ℤ
private def vacuumBlock : WeightBlocks D (0 : X) 0 := ⟨0, by simp⟩
private theorem step (i : Bool) : (0 : X) + D.α i = D.α i := zero_add _
private theorem step₂ (i j : Bool) : D.α j + D.α i = D.α j + D.α i := rfl
private theorem step₄ (i j : Bool) : D.α i + D.α j = D.α j + D.α i := add_comm _ _

private def sourceVacuum : ELVWeightProduct D (parameterTwist D Sc) (fun _ => 12) 12 (0 : X) 0 :=
  fun β => if hb : β.1 = 0 then
    (by rw [hb]; exact vacuumModule D (parameterTwist D Sc) (fun _ => 12) 12)
  else elvZeroModule D (parameterTwist D Sc) (fun _ => 12) 12 β.1

private def outputWord (i j : Bool) : ContentCategory D (parameterTwist D Sc) (fun _ => 12) 12
    (blockSucc₂ D i j (0 : X) (step j) (step₂ i j) vacuumBlock).1 where
  obj := ⟨[j,i]⟩
  content := by
    change ([j,i] : Multiset Bool) = ([i] : Multiset Bool) + (([j] : Multiset Bool) + 0)
    rw [add_zero]
    change ([j] : Multiset Bool) + ([i] : Multiset Bool) = ([i] : Multiset Bool) + ([j] : Multiset Bool)
    exact add_comm _ _

/-- Both connected mixed orders use the given weight crossings and the
original scalar polynomial on their actual supported output contents. -/
example := elvWeightCrossVia_quadratic_total D Sc (fun _ => 12) 12 true false (0 : X)
  (step false) (step₂ true false) (step true) (step₄ true false) (by decide)
  vacuumBlock _ rfl sourceVacuum (outputWord true false)

example := elvWeightCrossVia_quadratic_total D Sc (fun _ => 12) 12 false true (0 : X)
  (step true) (step₂ false true) (step false) (step₄ false true) (by decide)
  vacuumBlock _ rfl sourceVacuum (outputWord false true)

end OddMath.QuiverHecke.ELVWeightPairQuadraticExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightPairQuadratic
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
