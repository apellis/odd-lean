import OddMath.QuiverHecke.CyclotomicAction.ELVKernelDegree
noncomputable section
open OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous)

example (ν : List I) :
    ∃ L : ℤ, ∀ (cutoff : I → ℕ) (C : ℤ),
      (∀ j ∈ ν, C ≤ 2 * sy.d j * cutoff j) →
      ∀ v w : List I, v.Perm ν → w.Perm ν →
      ∀ n : ℤ, n < L + C + L →
      Function.Injective (fun x : elvHomDegree D sy Sc hc cutoff v w n =>
        (ideal D Sc cutoff v w).mkQ x.val) :=
  exists_old_degree_injective D sy Sc hc ν

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVKernelDegree
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
