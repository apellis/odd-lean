import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRepresentable

noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (σ : List I) (v : ContentCategory D Sc cutoff N β)

example :
    (contentInduction D Sc cutoff N β σ).obj (contentRepresentable D Sc cutoff N β v) ≅
      contentRepresentable D Sc cutoff N (β + (σ : Multiset I))
        ((contentAppend D Sc cutoff N β σ).obj v) :=
  InductionRepresentable.iso D Sc cutoff N β σ v

example (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (z : ContentCategory D Sc cutoff N β)
    (h : (contentAppend D Sc cutoff N β σ).obj z ⟶ w) (g : v ⟶ z) :
    InductionRepresentable.forward D Sc cutoff N β σ v w
      (BalancedInduction.tensor (contentAppend D Sc cutoff N β σ)
        (contentRepresentableFunctor D Sc cutoff N β v) z h g) =
      (contentAppend D Sc cutoff N β σ).map g ≫ h :=
  InductionRepresentable.forward_tensor D Sc cutoff N β σ v w z h g

#print axioms InductionRepresentable.iso
#print axioms InductionRepresentable.forward_mem
#print axioms InductionRepresentable.backward_mem

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionRepresentable
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
