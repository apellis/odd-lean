import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryNumeratorCoefficients
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v : List I) (d : ℕ) :
    appendC0 D Sc cutoff i v v
      (appendProjection D Sc cutoff i v (v ++ [i])
        (appendMovingPower D Sc cutoff i v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫ endpointELV D Sc cutoff i v)) =
    inputCoefficientShift D Sc cutoff i v d
      (orderedQPOutputCoefficients D Sc cutoff i v (List.range v.length)
        (endpointOutputCoefficients D Sc cutoff i v)) :=
  appendC0_orderedReverseNumerator D Sc cutoff i v d

example (i : I) (v : List I) :
    appendProjection D Sc cutoff i v (v ++ [i]) (endpointELV D Sc cutoff i v) =
    appendOutputEmbedding D Sc cutoff i v v (endpointOutputCoefficients D Sc cutoff i v) :=
  endpointOutputCoefficients_embedding D Sc cutoff i v

run_cmd do
  let env ← Lean.getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryNumeratorCoefficients
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  let mut count : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    Lean.logInfo m!"AUDIT {owner} {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Empty declaration inventory for {owner}"
  Lean.logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
