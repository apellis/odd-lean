import OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctIso
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace ContentDistinctIsoExamples
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
private def N (n : ℕ) (j : Bool) :=
  supermoduleParityObj ((BalancedInduction.restriction (oldContentInclusion D Sc (cutoff n) [j])).obj
    (oldRepresentable D Sc (cutoff n) (⟨[j]⟩ : OldCategory D Sc (cutoff n))))

/-- Both mixed moving parities preserve exactly the chosen module forward map. -/
example (n : ℕ) (i : Bool) := oldContentDistinctMateModuleIso D Sc (cutoff n)
  [] i (!i) (distinct i) (N n (!i))
example (n : ℕ) (i : Bool) := oldContentDistinctMateModuleIso_hom D Sc (cutoff n)
  [] i (!i) (distinct i) (N n (!i))
example (n : ℕ) (i : Bool) := oldContentDistinctMateModuleIso_inv_mem D Sc (cutoff n)
  [] i (!i) (distinct i) (N n (!i))
example (i : Bool) := oldContentDistinctMateModuleIso D Sc (cutoff 0)
  [] i (!i) (distinct i) (N 0 (!i))
example (n : ℕ) (i : Bool) := oldContentDistinctMateFunctorIso D Sc (cutoff n) [] i (!i) (distinct i)
example (n : ℕ) (i : Bool) := oldContentDistinctMateFunctorIso_hom_total D Sc (cutoff n)
  [] i (!i) (distinct i) (N n (!i))

private def allOddN (n : ℕ) :=
  supermoduleParityObj ((BalancedInduction.restriction
    (oldContentInclusion AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n) [true])).obj
      (oldRepresentable AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n)
        (⟨[true]⟩ : OldCategory AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n))))

/-- Distinct odd colours test the odd inverse and both complete functor roundtrips. -/
example (n : ℕ) := oldContentDistinctMateModuleIso_inv_mem AsymmetricParameters.datum
  AsymmetricParameters.scalars (cutoff n) [] false true (by decide) (allOddN n)
example (n : ℕ) := oldContentDistinctMateFunctorIso_inv_mem AsymmetricParameters.datum
  AsymmetricParameters.scalars (cutoff n) [] false true (by decide)
example (n : ℕ) := (oldContentDistinctMateFunctorIso AsymmetricParameters.datum
  AsymmetricParameters.scalars (cutoff n) [] false true (by decide)).hom_inv_id
example (n : ℕ) := (oldContentDistinctMateFunctorIso AsymmetricParameters.datum
  AsymmetricParameters.scalars (cutoff n) [] false true (by decide)).inv_hom_id

/-- Odd input-module maps retain the signed supernatural inverse law. -/
example (n : ℕ) := (oldContentDistinctMateFunctorIso AsymmetricParameters.datum
  AsymmetricParameters.scalars (cutoff n) [] false true (by decide)).inv.naturality 1
    (supermoduleParityIso (allOddN n)).hom (supermoduleParityIso_hom_mem (allOddN n))
end ContentDistinctIsoExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVRectangularMateIso,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctIso] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} declarations in {owner}"
