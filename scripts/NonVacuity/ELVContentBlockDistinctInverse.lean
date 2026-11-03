import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockDistinctInverse
import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace ContentBlockDistinctInverseConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut (n : ℕ) : Bool → ℕ := fun _ => n
private abbrev Q (n : ℕ) := oldTruncateFunctor D Sc (cut n) n
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide
private def M (n : ℕ) (j : Bool) := supermoduleParityObj
  ((BalancedInduction.restriction (contentInclusion D Sc (cut n) n (0 + ([j] : Multiset Bool)))).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc (cut n) n ((Q n).obj ⟨[j]⟩)))
private def empty (n : ℕ) : ContentCategory D Sc (cut n) n 0 := ⟨(Q n).obj ⟨[]⟩, by simp⟩
private def letter (n : ℕ) (i : Bool) : ContentCategory D Sc (cut n) n (0 + ([i] : Multiset Bool)) :=
  ⟨(Q n).obj ⟨[i]⟩, by simp⟩

/-- Both distinct mixed orders act on canonical truncated content modules. -/
example (n : ℕ) (i : Bool) := contentBlockDistinctMateLinear_square D Sc (cut n) n 0 i (!i)
  (M n (!i)) (letter n i)
example (n : ℕ) (i : Bool) := contentBlockDistinctMateLinear_bijective D Sc (cut n) n 0 i (!i)
  (distinct i) (M n (!i)) (letter n i)
example (n : ℕ) (i : Bool) := contentBlockDistinctMateModuleIso_hom D Sc (cut n) n 0 i (!i)
  (distinct i) (M n (!i))
example (n : ℕ) (i : Bool) := contentBlockDistinctMateModuleIso_inv_mem D Sc (cut n) n 0 i (!i)
  (distinct i) (M n (!i))
example (n : ℕ) (i : Bool) := (contentBlockDistinctMateModuleIso D Sc (cut n) n 0 i (!i)
  (distinct i) (M n (!i))).hom_inv_id
example (n : ℕ) (i : Bool) := (contentBlockDistinctMateModuleIso D Sc (cut n) n 0 i (!i)
  (distinct i) (M n (!i))).inv_hom_id
example (i : Bool) := contentBlockDistinctMateModuleIso D Sc (cut 0) 0 0 i (!i)
  (distinct i) (M 0 (!i))

private def exterior (n : ℕ) : (⟨[true]⟩ : OldCategory D Sc (cut n)) ⟶ ⟨[true]⟩ :=
  (ideal D Sc (cut n) [true] [true]).mkQ
    (SKM.SYM.elvCoefficientQuotient D (cut n) (SKM.SYM.delta D ℚ ⟨true, rfl⟩) ⊗ₜ[ℚ]
      𝟙 ((pres D Sc).obj (ob D [true])))
/-- An odd exterior input and its inhomogeneous identity sum retain their full chart formula. -/
example (n : ℕ) := contentBlockDistinctSourceNativeLinear_tensor D Sc (cut n) n 0 false true
  (M n true) (empty n) (letter n false) (𝟙 ((Q n).obj ⟨[false]⟩))
  ((Q n).map (𝟙 (⟨[true]⟩ : OldCategory D Sc (cut n)) + exterior n))

private def oddM (n : ℕ) := supermoduleParityObj
  ((BalancedInduction.restriction (contentInclusion AsymmetricParameters.datum
    AsymmetricParameters.scalars (cut n) n (0 + ([true] : Multiset Bool)))).obj
      (WeightedAppendFixture.truncatedRepresentable AsymmetricParameters.datum
        AsymmetricParameters.scalars (cut n) n
          ((oldTruncateFunctor AsymmetricParameters.datum AsymmetricParameters.scalars (cut n) n).obj ⟨[true]⟩)))

/-- Distinct odd colours retain the odd inverse and whole functor roundtrips. -/
example (n : ℕ) := contentBlockDistinctMateModuleIso_inv_mem AsymmetricParameters.datum
  AsymmetricParameters.scalars (cut n) n 0 false true (by decide) (oddM n)
example (n : ℕ) := contentBlockDistinctMateFunctorIso_inv_mem AsymmetricParameters.datum
  AsymmetricParameters.scalars (cut n) n 0 false true (by decide)
example (n : ℕ) := (contentBlockDistinctMateFunctorIso AsymmetricParameters.datum
  AsymmetricParameters.scalars (cut n) n 0 false true (by decide)).hom_inv_id
example (n : ℕ) := (contentBlockDistinctMateFunctorIso AsymmetricParameters.datum
  AsymmetricParameters.scalars (cut n) n 0 false true (by decide)).inv_hom_id
example (n : ℕ) := (contentBlockDistinctMateFunctorIso AsymmetricParameters.datum
  AsymmetricParameters.scalars (cut n) n 0 false true (by decide)).inv.naturality 1
    (supermoduleParityIso (oddM n)).hom (supermoduleParityIso_hom_mem (oddM n))
end ContentBlockDistinctInverseConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquareSource,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockDistinctMate,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockDistinctInverse] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
