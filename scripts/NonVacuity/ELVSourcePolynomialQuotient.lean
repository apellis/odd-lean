import OddMath.QuiverHecke.CyclotomicAction.ELVSourcePolynomialQuotient
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open CyclotomicCrossingTensor
namespace SourcePolynomialQuotientConsumer
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (p : ZMod 2) (i : I) (v : List I)

example (z : Target D Sc cutoff i v (v ++ [i])) :
    sourceQuotientEquiv D Sc cutoff p i v ((LinearMap.range (alpha D Sc cutoff i v v)).mkQ z) =
      outputLongExtraction D Sc cutoff p i v z := sourceQuotientEquiv_mk D Sc cutoff p i v z

example (z : Target D Sc cutoff i v (v ++ [i]) ⧸ LinearMap.range (alpha D Sc cutoff i v v)) :
    (sourceQuotientEquiv D Sc cutoff p i v).symm (sourceQuotientEquiv D Sc cutoff p i v z) = z :=
  (sourceQuotientEquiv D Sc cutoff p i v).symm_apply_apply z

example (f : ℕ →₀ Old D Sc cutoff v v) :
    sourceQuotientEquiv D Sc cutoff p i v
      ((LinearMap.range (alpha D Sc cutoff i v v)).mkQ (sourceLongSection D Sc cutoff p i v f)) = f := by
  rw [sourceQuotientEquiv_mk, outputLongExtraction_sourceLongSection]

example (j : {j : I // D.parity j = 1}) (a : PprimeDomain D Sc cutoff j.1 v v)
    (m : ℕ) (b : Old D Sc cutoff v v) :
    appendC0 D Sc cutoff j.1 v v (pMap D Sc cutoff j.1 v (v ++ [j.1])
      ((sourceCoordinateEquiv D Sc cutoff p j.1 v).symm (a, Finsupp.single m b))) =
        outputPolynomialBoundary D Sc cutoff p j v (Finsupp.single m b) :=
  appendC0_pMap_sourceCoordinates D Sc cutoff p j v a _

example (j : {j : I // D.parity j = 1}) :
    sourceQuotientBoundary D Sc cutoff j v = outputPolynomialBoundary D Sc cutoff p j v ∘ₗ
      (sourceQuotientEquiv D Sc cutoff p j.1 v).toLinearMap :=
  sourceQuotientBoundary_eq D Sc cutoff p j v

end SourcePolynomialQuotientConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVSourcePolynomialQuotient
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
