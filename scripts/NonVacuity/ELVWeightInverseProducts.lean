import OddMath.QuiverHecke.CyclotomicAction.ELVWeightInverseProducts
import OddMath.QuiverHecke.CyclotomicAction.ELVContentAbsentUnitInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import NonVacuity.ELVWeightedAppendFixture
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction BalancedInduction CyclotomicCrossingTensor
namespace WeightInverseProductsConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
/-- The index is infinite and the truncation bounds are unbounded. -/
private abbrev C (r : ℕ) := ContentModules D Sc cut (r + 4) 0
private def M (r : ℕ) : C r := supermoduleParityObj
  ((restriction (contentInclusion D Sc cut (r + 4) 0)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut (r + 4)
      ((oldTruncateFunctor D Sc cut (r + 4)).obj ⟨[]⟩)))
private def J (i : Bool) (r : ℕ) := Classical.choice
  (contentAbsentUnitInverse_nonempty D Sc cut (r + 4) 0 i (by simp) (M r))
/-- All constructed inverses have the common finite window despite varying categories. -/
private theorem window (i : Bool) : contentUnitCount D cut i 0 = 4 := rfl
private def productFrom (i : Bool) := SuperSumInvFrom.piOfCount
  (fun _ : ℕ => contentUnitCount D cut i 0) (fun _ => window i) (J i)
example (i : Bool) := (productFrom i).total
example (i : Bool) := (productFrom i).ff
example (i : Bool) := (productFrom i).f'_mem
example (i : Bool) (n : ℕ) := (productFrom i).g'_mem n
example (i : Bool) := (productFrom i).fg 0 (by cases i <;> decide)
example (i : Bool) := (productFrom i).gf 1 (by cases i <;> decide)
example (i : Bool) := (productFrom i).gg 0 1 (by cases i <;> decide) (by cases i <;> decide)
/-- The row constructor also consumes constructed inverse data, with the two directions exchanged. -/
private def reciprocal (i : Bool) (r : ℕ) :
    SuperSumInvTo (k := ℚ) (J i r).f' (J i r).g' (D.parity i)
      (fun n => n • D.parity i) (contentUnitCount D cut i 0) where
  f' := 0
  g' := fun n => unitDotColumn
    (contentAppendTo D Sc cut (r + 4) 0 [i] (0 + ([i] : Multiset Bool)) (contentBlockCanonicalSum 0 [i]))
    (contentBlockMatrixDot_supernatural D Sc cut (r + 4) 0 i) (M r) n
  f_mem := (J i r).f'_mem
  g_mem := (J i r).g'_mem
  f'_mem := (J i r).f_mem
  g'_mem := (J i r).g_mem
  total := (J i r).total
  ff := (J i r).ff
  fg := (J i r).fg
  gf := (J i r).gf
  gg := (J i r).gg
private def productTo (i : Bool) := SuperSumInvTo.piOfCount
  (fun _ : ℕ => contentUnitCount D cut i 0) (fun _ => window i) (reciprocal i)
example (i : Bool) := (productTo i).total
example (i : Bool) := (productTo i).ff
example (i : Bool) := (productTo i).f'_mem
example (i : Bool) (n : ℕ) := (productTo i).g'_mem n
example (i : Bool) := (productTo i).gg 1 0 (by cases i <;> decide) (by cases i <;> decide)
end WeightInverseProductsConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVWeightInverseProducts
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"
