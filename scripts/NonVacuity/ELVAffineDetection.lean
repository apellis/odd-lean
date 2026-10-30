import OddMath.QuiverHecke.CyclotomicAction.ELVAffineDetection
noncomputable section
open OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [Field k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous)

include hc in
example (ν : List I) (B : ℤ) :
    ∃ K : ℕ, ∀ (cutoff : I → ℕ) (N : ℕ),
      (∀ j ∈ ν, K ≤ cutoff j) → K ≤ N →
      ∀ v w : List I, v.Perm ν → w.Perm ν →
      Function.Injective (fun x : affinePBWDegreeBelow D sy Sc v w B =>
        (truncatedIdeal D Sc cutoff N v w).mkQ (affineUnit D Sc cutoff v w x.val)) :=
  affinePBW_detected_at_high_cutoffs D sy Sc hc ν B

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVLowerDegree,
    `OddMath.QuiverHecke.CyclotomicAction.ELVKernelDegree,
    `OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedKernelDegree,
    `OddMath.QuiverHecke.CyclotomicAction.ELVAffineDetection]
  for owner in owners do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Module was not imported: {owner}"
    let mut count : Nat := 0
    for name in env.header.moduleData[idx]!.constNames do
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      count := count + 1
    if count == 0 then throwError "Empty declaration inventory: {owner}"
    logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
