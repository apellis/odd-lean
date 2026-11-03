import OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctMate
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open CyclotomicCrossingTensor
namespace ContentDistinctMateExamples
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
private def s (n : ℕ) : OldContentCategory D Sc (cutoff n) [] := ⟨⟨[]⟩, List.Perm.refl []⟩
private def t (n : ℕ) (i : Bool) : OldContentCategory D Sc (cutoff n) [i] :=
  ⟨⟨[i]⟩, List.Perm.refl [i]⟩
private def N (n : ℕ) (j : Bool) :=
  supermoduleParityObj ((BalancedInduction.restriction (oldContentInclusion D Sc (cutoff n) [j])).obj
    (oldRepresentable D Sc (cutoff n) (⟨[j]⟩ : OldCategory D Sc (cutoff n))))
private def b (n : ℕ) (j : Bool) :
    (N n j).obj ((oldContentAppend D Sc (cutoff n) [] j).obj (s n)) :=
  𝟙 (⟨[j]⟩ : OldCategory D Sc (cutoff n))
private def exteriorEnd (n : ℕ) (i : Bool) :
    (⟨[i]⟩ : OldCategory D Sc (cutoff n)) ⟶ ⟨[i]⟩ :=
  (ideal D Sc (cutoff n) [i] [i]).mkQ
    (SKM.SYM.elvCoefficientQuotient D (cutoff n) (SKM.SYM.delta D ℚ ⟨true, rfl⟩) ⊗ₜ[ℚ]
      𝟙 ((pres D Sc).obj (ob D [i])))

/-- The positive rectangular content mate keeps a complete odd exterior arrow. -/
example (n : ℕ) (i : Bool) := BalancedInduction.orderedRectangularMateComponent_total_tensor
  (k := ℚ) (oldContentAppend D Sc (cutoff n) [] (!i))
  (oldContentAppend D Sc (cutoff n) [] i) (oldContentAppend D Sc (cutoff n) [!i] i)
  (oldContentDistinctUpperAppend D Sc (cutoff n) [] i (!i))
  (oldContentDistinctCross_supernatural D Sc (cutoff n) [] i (!i))
  (N n (!i)) (s n) (t n i) (exteriorEnd n i) (b n (!i))
example (n : ℕ) (i : Bool) := oldContentDistinctSourceLinear_tensor D Sc (cutoff n)
  [] i (!i) (N n (!i)) (s n) (t n i) (exteriorEnd n i) (b n (!i))
example (n : ℕ) (i : Bool) := oldContentDistinctSourceIso D Sc (cutoff n) [] i (!i) (N n (!i))
example (n : ℕ) (i : Bool) := oldContentDistinctTargetIso D Sc (cutoff n) [] i (!i) (N n (!i))
example (i : Bool) := oldContentDistinctMateComponent D Sc (cutoff 0) [] i (!i) (N 0 (!i))

/-- The nontrivial crossing parity also acts on the entire fixed-content module. -/
example (n : ℕ) := oldContentDistinctMateComponent AsymmetricParameters.datum
  AsymmetricParameters.scalars (cutoff n) [] false true
  (supermoduleParityObj ((BalancedInduction.restriction
    (oldContentInclusion AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n) [true])).obj
      (oldRepresentable AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n)
        (⟨[true]⟩ : OldCategory AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n)))))
end ContentDistinctMateExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVOldContentAppendTo,
      `OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularMate,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentDistinctMate] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} declarations in {owner}"
