import NonVacuity.ELVCyclotomicPprime
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicShortColumns

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor
namespace ShortColumnConsumer
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (i : I) (v s t : List I)

theorem leftSquare :
    pMap D Sc cutoff i v (t ++ [i]) ∘ₗ alpha D Sc cutoff i v t =
      shortCross D Sc cutoff i v t ∘ₗ pprime D Sc cutoff i v t :=
  shortColumn_square D Sc cutoff i v t

theorem rightSquare :
    canonicalAppendTarget D Sc cutoff i v (t ++ [i]) ∘ₗ shortCross D Sc cutoff i v t =
      toCyclotomic D Sc cutoff i v t ∘ₗ q D Sc cutoff i v t :=
  shortColumn_quotient_square D Sc cutoff i v t

theorem alphaFormula (h : hom D Sc cutoff (i :: s) t)
    (b : hom D Sc cutoff v (s ++ [i])) :
    alpha D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s t h
      ((ideal D Sc cutoff _ _).mkQ b)) =
    projection D Sc cutoff i v (t ++ [i])
      (insert D Sc cutoff i _ _ (twist k (epsilon D cutoff i v) b) ≫
        rightContext D Sc cutoff [i] _ _ h) := by
  rw [alpha_tensor, alphaPair_mk]

theorem crossingFormula (c : hom D Sc cutoff (s ++ [i]) t)
    (b : hom D Sc cutoff v (s ++ [i])) :
    shortCross D Sc cutoff i v t (shortTensor D Sc cutoff i v s t c
      ((ideal D Sc cutoff _ _).mkQ b)) =
    appendProjection D Sc cutoff i v (t ++ [i])
      (rightContext D Sc cutoff [i] _ _ b ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ c) := by
  rw [shortCross_tensor, shortCrossPair_mk]

theorem rightExactRows :
    (LinearMap.range (pprime D Sc cutoff i v t) = LinearMap.ker (q D Sc cutoff i v t)) ∧
    Function.Surjective (q D Sc cutoff i v t) ∧
    (LinearMap.ker (canonicalAppendTarget D Sc cutoff i v (t ++ [i])) =
      LinearMap.range (pMap D Sc cutoff i v (t ++ [i]))) ∧
    Function.Surjective (canonicalAppendTarget D Sc cutoff i v (t ++ [i])) :=
  ⟨range_pprime_eq_ker_q D Sc cutoff i v t, q_surjective D Sc cutoff i v t,
    ker_canonicalAppendTarget D Sc cutoff i v (t ++ [i]),
    canonicalAppendTarget_surjective D Sc cutoff i v (t ++ [i])⟩

end ShortColumnConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicShortColumns
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
