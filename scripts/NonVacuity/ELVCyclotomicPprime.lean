import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicPprime

noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor
namespace PprimeConsumer
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (i : I) (v s t : List I)

theorem movingFormula (h : hom D Sc cutoff (i :: s) t) (b : Old D Sc cutoff v (s ++ [i])) :
    pprime D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s t h b) =
      shortTensor D Sc cutoff i v s t (appendW D Sc cutoff i s ≫ h) b :=
  pprime_tensor D Sc cutoff i v s t h b

theorem fullBalance (s' : List I) (r : hom D Sc cutoff s s')
    (h : hom D Sc cutoff (i :: s') t) (b : Old D Sc cutoff v (s ++ [i])) :
    pprimeSummand D Sc cutoff i v s t ((insert D Sc cutoff i s s' r ≫ h) ⊗ₜ[k] b) =
      pprimeSummand D Sc cutoff i v s' t (h ⊗ₜ[k]
        (coefficient D Sc cutoff (epsilon D cutoff i v) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) :=
  pprimeSummand_balance D Sc cutoff i v s s' t r h b

theorem rangeSpan : LinearMap.range (pprime D Sc cutoff i v t) = movingImage D Sc cutoff i v t :=
  range_pprime D Sc cutoff i v t

theorem exactness : LinearMap.range (pprime D Sc cutoff i v t) = LinearMap.ker (q D Sc cutoff i v t) :=
  range_pprime_eq_ker_q D Sc cutoff i v t

theorem quotientKills (z : PprimeDomain D Sc cutoff i v t) :
    q D Sc cutoff i v t (pprime D Sc cutoff i v t z) = 0 := by
  apply LinearMap.mem_ker.mp
  rw [← range_pprime_eq_ker_q]
  exact ⟨z, rfl⟩

theorem quotientSurjective : Function.Surjective (q D Sc cutoff i v t) := q_surjective D Sc cutoff i v t

theorem quotientFormula (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    q D Sc cutoff i v t (shortTensor D Sc cutoff i v s t c b) =
      tensor D Sc cutoff i v s t ((ideal D Sc cutoff _ _).mkQ c) b :=
  q_shortTensor D Sc cutoff i v s t c b

end PprimeConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicPprime
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
