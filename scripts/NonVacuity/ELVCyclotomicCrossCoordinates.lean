import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicCrossCoordinates
import Lean.Util.CollectAxioms

/-! Consumers of the prescribed balanced source over arbitrary full coefficients. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor ShortCrossCoordinates
namespace CrossExtractionConsumer
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (i : I) (v s t : List I)

def decoder : AppendTarget D Sc cutoff i v (t ++ [i]) →ₗ[k] ShortTarget D Sc cutoff i v t :=
  decode D Sc cutoff i v t

theorem arbitraryClass (z : ShortTarget D Sc cutoff i v t) :
    decoder D Sc cutoff i v t (shortCross D Sc cutoff i v t z) = z :=
  decode_shortCross D Sc cutoff i v t z

theorem representative (c : hom D Sc cutoff (s ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    decoder D Sc cutoff i v t (shortCrossPair D Sc cutoff i v s t c b) =
      shortTensor D Sc cutoff i v s t c b := by
  rw [← shortCross_tensor]
  exact arbitraryClass D Sc cutoff i v t _

theorem actualColumn : Function.Injective (shortCross D Sc cutoff i v t) :=
  shortCross_injective D Sc cutoff i v t

theorem actualRange : LinearMap.range (shortCross D Sc cutoff i v t) =
    appendCrossingSpan D Sc cutoff i v t := range_shortCross D Sc cutoff i v t

def actualSourceEquiv : ShortTarget D Sc cutoff i v t ≃ₗ[k] appendCrossingSpan D Sc cutoff i v t :=
  crossingEquiv D Sc cutoff i v t

theorem correction (r : hom D Sc cutoff v (s ++ [i]))
    (g : hom D Sc cutoff (s ++ [i]) t) (m : ℕ) :
    decoder D Sc cutoff i v t
      (appendProjection D Sc cutoff i v (t ++ [i])
        (rightContext D Sc cutoff [i] _ _ r ≫ appendOutputPolynomial D Sc cutoff i (s ++ [i]) t
          (appendCrossingCorrection D Sc cutoff i s t m g))) = 0 :=
  decode_outputPolynomial_precomp D Sc cutoff i v (s ++ [i]) t r _

end CrossExtractionConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicCrossCoordinates
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing production module {owner}"
  let mut count : Nat := 0
  let mut privateCount : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    count := count + 1
    if name.getRoot == `_private then privateCount := privateCount + 1
  if count == 0 then throwError "Empty declaration inventory: {owner}"
  if privateCount == 0 then throwError "Private declarations absent: {owner}"
  logInfo m!"Audited {count} declarations owned by {owner}, including {privateCount} private declarations; all transitive axioms allowed."

#print axioms OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.ShortCrossCoordinates.decode_comp_shortCross
#print axioms OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.ShortCrossCoordinates.shortCross_injective
#print axioms OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.ShortCrossCoordinates.range_shortCross
#print axioms OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.ShortCrossCoordinates.crossingEquiv
