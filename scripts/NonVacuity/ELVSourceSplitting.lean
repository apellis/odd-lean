import OddMath.QuiverHecke.CyclotomicAction.ELVSourceSplitting
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor
namespace SourceSplittingConsumer
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (p : ZMod 2) (i : I) (v s t : List I)

example : LinearMap.range (alpha D Sc cutoff i v t) = chronologicalShortSpan D Sc cutoff i v t :=
  range_alpha_eq_chronologicalShortSpan D Sc cutoff i v t

example (z : Target D Sc cutoff i v (v ++ [i])) :
    (sourceCoordinateEquiv D Sc cutoff p i v).symm
      (extract D Sc cutoff i v v z, outputLongExtraction D Sc cutoff p i v z) = z :=
  (sourceCoordinateEquiv D Sc cutoff p i v).symm_apply_apply z

example (a : PprimeDomain D Sc cutoff i v v) (f : ℕ →₀ Old D Sc cutoff v v) :
    sourceCoordinateEquiv D Sc cutoff p i v
      (alpha D Sc cutoff i v v a + sourceLongSection D Sc cutoff p i v f) = (a, f) :=
  (sourceCoordinateEquiv D Sc cutoff p i v).apply_symm_apply (a, f)

example (h : hom D Sc cutoff (i :: s) v) (b : Old D Sc cutoff v (s ++ [i])) :
    sourceCoordinateEquiv D Sc cutoff p i v (alphaPair D Sc cutoff i v s v h b) =
      (pprimeTensor D Sc cutoff i v s v h b, 0) := by
  rw [← alpha_tensor, sourceCoordinateEquiv_alpha]

example (m : ℕ) (b : Old D Sc cutoff v v) :
    outputLongExtraction D Sc cutoff p i v
      (sourceLongSection D Sc cutoff p i v (Finsupp.single m b)) = Finsupp.single m b :=
  outputLongExtraction_sourceLongSection D Sc cutoff p i v _

example (a : PprimeDomain D Sc cutoff i v v) (f : ℕ →₀ Old D Sc cutoff v v) :
    pMap D Sc cutoff i v (v ++ [i]) ((sourceCoordinateEquiv D Sc cutoff p i v).symm (a, f)) =
      shortCross D Sc cutoff i v v (pprime D Sc cutoff i v v a) +
        pMap D Sc cutoff i v (v ++ [i]) (sourceLongSection D Sc cutoff p i v f) :=
  pMap_sourceCoordinateEquiv_symm D Sc cutoff p i v a f

end SourceSplittingConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVSourceSplitting
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
  logInfo m!"Audited {count} declarations owned by {owner}, including {privateCount} private declarations; all transitive axioms allowed."
