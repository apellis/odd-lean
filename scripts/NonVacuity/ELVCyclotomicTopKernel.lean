import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicTopKernel

noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (i : I) (v s t : List I)

example : Function.Surjective (q D Sc cutoff i v t) := q_surjective D Sc cutoff i v t

example : LinearMap.ker (q D Sc cutoff i v t) = firstIdeal D Sc cutoff i v t :=
  ker_q D Sc cutoff i v t

example : LinearMap.ker (q D Sc cutoff i v t) = movingImage D Sc cutoff i v t :=
  ker_q_eq_movingImage D Sc cutoff i v t

example : (ShortTarget D Sc cutoff i v t ⧸ movingImage D Sc cutoff i v t) ≃ₗ[k]
    Source D Sc cutoff i v t := quotientEquiv D Sc cutoff i v t

example (c : hom D Sc cutoff (s ++ [i]) t) (b : hom D Sc cutoff v (s ++ [i])) :
    toCyclotomic D Sc cutoff i v t
      (q D Sc cutoff i v t (shortTensor D Sc cutoff i v s t c
        ((ideal D Sc cutoff _ _).mkQ b))) =
    (ideal D Sc cutoff (v ++ [i]) (t ++ [i])).mkQ
      (rightContext D Sc cutoff [i] _ _ b ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ c) :=
  toCyclotomic_q_shortTensor D Sc cutoff i v s t c b

example (h : hom D Sc cutoff (i :: s) t) (b : Old D Sc cutoff v (s ++ [i])) :
    q D Sc cutoff i v t
      (shortTensor D Sc cutoff i v s t (appendW D Sc cutoff i s ≫ h) b) = 0 := by
  apply LinearMap.mem_ker.mp
  rw [ker_q_eq_movingImage]
  exact Submodule.subset_span ⟨s, h, b, rfl⟩

example (c : hom D Sc cutoff [i] t) (b : Old D Sc cutoff v [i]) :
    q D Sc cutoff i v t (shortTensor D Sc cutoff i v [] t c b) =
      tensor D Sc cutoff i v [] t ((ideal D Sc cutoff _ _).mkQ c) b :=
  q_shortTensor D Sc cutoff i v [] t c b

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicCrossingTensor,
    `OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicTopQuotient,
    `OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicTopKernel]
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
