import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicAlphaCoordinates
import Lean.Util.CollectAxioms

/-! Generic consumers of the actual maps; no nonzero model is asserted. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor
namespace AlphaExtractionConsumer
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (i : I) (v s t : List I)

/-- The declared map has exactly the prescribed source and target. -/
def decoder : Target D Sc cutoff i v (t ++ [i]) →ₗ[k] PprimeDomain D Sc cutoff i v t :=
  extract D Sc cutoff i v t

theorem arbitraryClass (z : PprimeDomain D Sc cutoff i v t) :
    decoder D Sc cutoff i v t (alpha D Sc cutoff i v t z) = z :=
  extract_alpha D Sc cutoff i v t z

theorem representative (h : hom D Sc cutoff (i :: s) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    decoder D Sc cutoff i v t (alphaPair D Sc cutoff i v s t h b) =
      pprimeTensor D Sc cutoff i v s t h b := by
  rw [← alpha_tensor]
  exact arbitraryClass D Sc cutoff i v t _

theorem actualColumns : Function.Injective (alpha D Sc cutoff i v t) ∧
    Function.Injective (pprime D Sc cutoff i v t) :=
  ⟨alpha_injective D Sc cutoff i v t, pprime_injective D Sc cutoff i v t⟩

/-- The existing right-exact sequence now has an injective first map. -/
theorem shortExact : Function.Injective (pprime D Sc cutoff i v t) ∧
    LinearMap.range (pprime D Sc cutoff i v t) = LinearMap.ker (q D Sc cutoff i v t) ∧
    Function.Surjective (q D Sc cutoff i v t) :=
  ⟨pprime_injective D Sc cutoff i v t, range_pprime_eq_ker_q D Sc cutoff i v t,
    q_surjective D Sc cutoff i v t⟩

end AlphaExtractionConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicAlphaCoordinates
  let mut count : Nat := 0
  let mut privateCount : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! == owner then
        for axiomName in (← Lean.collectAxioms name) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
        count := count + 1
        if name.getRoot == `_private then privateCount := privateCount + 1
  if count == 0 then throwError "Empty declaration inventory: {owner}"
  if privateCount == 0 then throwError "Private declarations absent: {owner}"
  logInfo m!"Audited {count} declarations owned by {owner}, including {privateCount} private declarations; all transitive axioms allowed."

#print axioms OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.extract_comp_alpha
#print axioms OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.alpha_injective
#print axioms OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.pprime_injective
