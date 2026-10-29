import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedAppendTransform
import NonVacuity.ELVTruncatedCategory
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
namespace ELVTruncatedAppendConsumer
open ELVCoefficientCategoryConsumer ELVCoefficientGradingConsumer ELVHomGradingConsumer
local instance : GradedSupercategory ℚ (TruncatedCategory datum scalars (fun _ => 2) 3) :=
  truncatedGradedSupercategory datum scalars (fun _ => 2) 3 sy homogeneous

/-- An arbitrary-length spectator word, not a finite list of tested lengths. -/
def append (σ : List Unit) :=
  truncatedAppendGraded datum scalars (fun _ => 2) 3 sy homogeneous σ

example (σ v : List Unit) :
    ((append σ).obj ⟨v⟩).word = v ++ σ := rfl

/-- The existing exterior witness tests the coefficient contribution to parity. -/
theorem appendedOdd_parity (σ : List Unit) :
    (truncatedAppend datum scalars (fun _ => 2) 3 σ).map
      (ELVTruncatedCategoryConsumer.oddWitness :
        (⟨[()]⟩ : TruncatedCategory datum scalars (fun _ => 2) 3) ⟶ ⟨[()]⟩) ∈
      truncatedParity datum scalars (fun _ => 2) 3 ([()] ++ σ) ([()] ++ σ) 1 :=
  IsSuperfunctor.map_mem (F := truncatedAppend datum scalars (fun _ => 2) 3 σ)
    (X := ⟨[()]⟩) (Y := ⟨[()]⟩) ELVTruncatedCategoryConsumer.oddWitness_parity

/-- Naturality against the odd coefficient has the negative sign. -/
theorem dot_oddCoefficient :
    (truncatedAppend datum scalars (fun _ => 2) 3 [()]).map
      (ELVTruncatedCategoryConsumer.oddWitness :
        (⟨[()]⟩ : TruncatedCategory datum scalars (fun _ => 2) 3) ⟶ ⟨[()]⟩) ≫
      (truncatedAppendDot datum scalars (fun _ => 2) 3 ()).app 1 ⟨[()]⟩ =
    -((truncatedAppendDot datum scalars (fun _ => 2) 3 ()).app 1 ⟨[()]⟩ ≫
      (truncatedAppend datum scalars (fun _ => 2) 3 [()]).map
        (ELVTruncatedCategoryConsumer.oddWitness :
          (⟨[()]⟩ : TruncatedCategory datum scalars (fun _ => 2) 3) ⟶ ⟨[()]⟩)) := by
  have h := (truncatedAppendDot datum scalars (fun _ => 2) 3 ()).naturality
    1 (X := ⟨[()]⟩) (Y := ⟨[()]⟩) (q := 1) ELVTruncatedCategoryConsumer.oddWitness
    ELVTruncatedCategoryConsumer.oddWitness_parity
  simpa only [koszulSign_one_one, neg_one_smul] using h

example (v : TruncatedCategory datum scalars (fun _ => 2) 3) :
    (truncatedAppendDot datum scalars (fun _ => 2) 3 ()).app 1 v ∈
      truncatedDegree datum scalars (fun _ => 2) sy homogeneous 3
        (v.word ++ [()]) (v.word ++ [()]) 2 :=
  truncatedAppendDot_degree datum scalars (fun _ => 2) 3 sy homogeneous () v

example (v : TruncatedCategory datum scalars (fun _ => 2) 3) :
    (truncatedAppendCross datum scalars (fun _ => 2) 3 () ()).app 1 v ∈
      truncatedDegree datum scalars (fun _ => 2) sy homogeneous 3
        (v.word ++ [(), ()]) (v.word ++ [(), ()]) (-2) :=
  truncatedAppendCross_degree datum scalars (fun _ => 2) 3 sy homogeneous () () v

end ELVTruncatedAppendConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedAppend,
    `OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedAppendTransform]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if owners.contains modules[idx.toNat]! then
        for ax in ← Lean.collectAxioms name do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "No owned declarations audited"
  for name in #[`ELVTruncatedAppendConsumer.appendedOdd_parity,
      `ELVTruncatedAppendConsumer.dot_oddCoefficient] do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {count} owned declarations, including generated/private declarations, and two odd coefficient consumer theorems."
