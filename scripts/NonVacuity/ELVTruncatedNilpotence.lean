import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedNilpotence

noncomputable section
open CategoryTheory OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ)

example [Finite I] (ν : List I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (v : List I), v.Perm ν → ∀ (d : ℤ), 0 < d →
      ∀ f : TruncatedEnd D Sc cutoff N v,
        f ∈ truncatedEndDegree D Sc cutoff N sy hc v d → f ^ e = 0 :=
  truncatedContent_positive_pow_zero D Sc cutoff sy hc N ν

include sy hc in
example [Finite I] (v : List I) (r : ℕ) (i : I) (hi : v[r]? = some i) :
    IsNilpotent (truncatedDot D Sc cutoff N v r) := by
  obtain ⟨e, _, he⟩ := truncatedContent_dot_pow_zero D Sc cutoff sy hc N v
  exact ⟨e, he v (List.Perm.refl _) r i hi⟩

include sy hc in
example [Finite I] (i : I) (v : TruncatedCategory D Sc cutoff N) :
    let f : TruncatedEnd D Sc cutoff N (v.word ++ [i]) :=
      (truncatedAppendDot D Sc cutoff N i).app (D.parity i) v
    IsNilpotent f := by
  obtain ⟨e, _, he⟩ := truncatedAppendDot_pow_zero D Sc cutoff sy hc N v.word i
  exact ⟨e, he v (List.Perm.refl _)⟩

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedNilpotence
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
