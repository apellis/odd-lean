import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppendTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockRestrictionTensor
import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVContentParity
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace ContentBlockAppendConsumer
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut (n : ℕ) : Bool → ℕ := fun _ => n
private def M (n : ℕ) (β : Multiset Bool) :=
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc (cut n) n β)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc (cut n) n
      ((oldTruncateFunctor D Sc (cut n) n).obj ⟨[]⟩)))

/-- Exact multiset content retains the chosen full-inclusion unit and supported counit. -/
example (n : ℕ) (β : Multiset Bool) := contentExtensionUnitIso D Sc (cut n) n β (M n β)
example (n : ℕ) (β : Multiset Bool) := contentExtension_supported D Sc (cut n) n β (M n β)
example (n : ℕ) (β : Multiset Bool) := contentSupportedCounitIso D Sc (cut n) n β
  (BalancedInduction.induced (contentInclusion D Sc (cut n) n β) (M n β))
  (contentExtension_supported D Sc (cut n) n β (M n β))
example (n : ℕ) (β : Multiset Bool) := contentSupportedCounitIso_hom D Sc (cut n) n β
  (BalancedInduction.induced (contentInclusion D Sc (cut n) n β) (M n β))
  (contentExtension_supported D Sc (cut n) n β (M n β))

/-- Both moving parities use the literal append square and selected extension chart. -/
example (n : ℕ) (i : Bool) (β : Multiset Bool) := contentAppendToExtensionIso D Sc (cut n) n
  β [i] (β + ([i] : Multiset Bool)) rfl
example (n : ℕ) (i : Bool) (β : Multiset Bool) := contentAppendToRestrictionIso D Sc (cut n) n
  β [i] (β + ([i] : Multiset Bool)) rfl (M n β)
example (n : ℕ) (i : Bool) (β : Multiset Bool) := contentAppendToRestrictionExtensionIso D Sc (cut n) n
  β i (β + ([i] : Multiset Bool)) rfl (M n (β + ([i] : Multiset Bool)))
example (n : ℕ) (i : Bool) (β : Multiset Bool) :=
  (contentAppendToRestrictionExtensionIso D Sc (cut n) n β i
    (β + ([i] : Multiset Bool)) rfl (M n (β + ([i] : Multiset Bool)))).hom_inv_id

/-- Empty content and zero cutoff retain their genuine module domains. -/
example := contentAppendToRestrictionExtensionIso D Sc (cut 0) 0 0 true
  ([true] : Multiset Bool) (by simp) (M 0 [true])
/-- The restriction chart retains whole quotient-arrow generators. -/
example (n : ℕ) (β : Multiset Bool) (i : Bool)
    (w : TruncatedCategory D Sc (cut n) n) (s : ContentCategory D Sc (cut n) n β)
    (g : s.obj ⟶ w) (b : (M n (β + ([i] : Multiset Bool))).obj
      ((contentAppend D Sc (cut n) n β [i]).obj s)) :=
  contentAppendToRestrictionExtensionIso_tensor D Sc (cut n) n β i
    (β + ([i] : Multiset Bool)) rfl (M n (β + ([i] : Multiset Bool))) w s g b
/-- The selected append chart inserts its actual input inclusion unit. -/
example (n : ℕ) (β : Multiset Bool) (i : Bool)
    (s : ContentCategory D Sc (cut n) n β)
    (t : ContentCategory D Sc (cut n) n (β + ([i] : Multiset Bool)))
    (g : (truncatedAppend D Sc (cut n) n [i]).obj s.obj ⟶ t.obj) (b : (M n β).obj s) :=
  contentAppendToRestrictionLinear_tensor D Sc (cut n) n β [i]
    (β + ([i] : Multiset Bool)) rfl (M n β) s t g b
example (n : ℕ) (β : Multiset Bool) (i : Bool)
    (t : ContentCategory D Sc (cut n) n (β + ([i] : Multiset Bool))) :=
  contentAppendToRestrictionLinear_eq_selected D Sc (cut n) n β [i]
    (β + ([i] : Multiset Bool)) rfl (M n β) t
end ContentBlockAppendConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockExtension,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppend,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockRestrictionTensor,
      `OddMath.QuiverHecke.CyclotomicAction.ELVFullInductionSquare,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentBlockAppendTensor] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} owned declarations in {owner}"
