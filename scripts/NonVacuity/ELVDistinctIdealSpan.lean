import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctIdealSpan
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace DistinctIdealSpanExamples

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
private def cutoff (n : ℕ) (_ : Bool) := n
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide
private def oldTarget (i : Bool) : List Bool := if i then [true, true] else [false, false]

/-- The literal two-outer-ideal equality for both mixed moving parities and
matching nonempty corners with repeated colours. -/
example (n : ℕ) (i : Bool) :=
  ideal_eq_appendRelations_sup_outputOldRelations D Sc (cutoff n) i (!i) (distinct i)
    [false, true] (oldTarget i)

/-- There is no old first-position relation in the vacuum boundary; zero
cutoffs do not introduce an exception to the mixed corner equality. -/
example (i : Bool) :=
  ideal_eq_appendRelations_sup_outputOldRelations D Sc (cutoff 0) i (!i) (distinct i) [] []

private def oddCoefficient (n : ℕ) : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D (cutoff n) :=
  SKM.SYM.elvCoefficientQuotient D (cutoff n) (SKM.SYM.delta D ℚ ⟨true, rfl⟩)

private def crossing (n : ℕ) (i : Bool) :
    hom D Sc (cutoff n) (i :: [!i, i]) ([i, i] ++ [!i]) :=
  oddCoefficient n ⊗ₜ[ℚ] crossLast D Sc [i] (!i) i

/-- A concrete nonidentity crossing with a full exterior coefficient lies
in the old-output relation span, for even and odd cutoffs. -/
example (i : Bool) := relation_comp_outputOldRelations D Sc (cutoff 5)
  i (!i) (distinct i) [!i, i] [i, i] (crossing 5 i)

example (i : Bool) := relation_comp_outputOldRelations D Sc (cutoff 6)
  i (!i) (distinct i) [!i, i] [i, i] (crossing 6 i)

example (i : Bool) := appendW_range_le_outputOldRelations D Sc (cutoff 5)
  i (!i) (distinct i) [!i, i] [i, i]

end DistinctIdealSpanExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVOutputLastShuffle,
      `OddMath.QuiverHecke.CyclotomicAction.ELVDistinctIdealSpan] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} declarations in {owner}"
