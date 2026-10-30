import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryPolynomial
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    appendC0 D Sc cutoff j.1 v v (pMap D Sc cutoff j.1 v (v ++ [j.1]) z) =
      outputPolynomialBoundary D Sc cutoff p j v
        (outputLongExtraction D Sc cutoff p j.1 v z) :=
  appendC0_pMap D Sc cutoff p j v z

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    SKM.zsign k (D.parity j.1) ^ v.count j.1 •
      outputPolynomialBoundary D Sc cutoff p j v
        (∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          Finsupp.mapRange.linearMap
            ((oldComp D Sc cutoff v v v).flip (independentOutputS D Sc cutoff j.1 v n))
            ((outputCoefficientRho D Sc cutoff p j v)^[n]
              (outputLongExtraction D Sc cutoff p j.1 v
                (outputCorrectedLift D Sc cutoff p j v d
                  ((ideal D Sc cutoff v v).mkQ (𝟙 _)))))) =
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      appendC0 D Sc cutoff j.1 v v
        (appendProjection D Sc cutoff j.1 v (v ++ [j.1])
          (appendMovingPower D Sc cutoff j.1 v d ≫
            affineUnit D Sc cutoff _ _ (appendQPProduct D Sc j.1 v) ≫
            endpointELV D Sc cutoff j.1 v)) :=
  outputPolynomialBoundary_independentS D Sc cutoff p j v d

run_cmd do
  let env ← Lean.getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryPolynomial
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
