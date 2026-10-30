import OddMath.QuiverHecke.CyclotomicAction.ELVOutputSIterates
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v : List I) (n : ℕ) (q : ZMod 2) :
    oldTwist D Sc cutoff q v v (independentOutputS D Sc cutoff i v n) =
      independentOutputS D Sc cutoff i v n :=
  independentOutputS_oldTwist D Sc cutoff i v n q

example (i : I) (hi : D.parity i = 1)
    (v : List I) {n : ℕ} (hn : n ∈ (independentOutputS D Sc cutoff i v).support) :
    Even n :=
  independentOutputS_support_even D Sc cutoff i hi v hn

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ)
    (z : Target D Sc cutoff j.1 v (v ++ [j.1])) :
    outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d] z) =
      (outputCoefficientRho D Sc cutoff p j v)^[d]
        (outputLongExtraction D Sc cutoff p j.1 v z) :=
  outputLongExtraction_boundaryRho_iterate D Sc cutoff p j v d z

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (n : ℕ) (hn : Even n)
    (b : Old D Sc cutoff v v) :
    (outputCoefficientRho D Sc cutoff p j v)^[n] (Finsupp.single 0 b) =
      Finsupp.single n b :=
  outputCoefficientRho_iterate_even_single D Sc cutoff p j v n hn b

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    (outputCoefficientRho D Sc cutoff p j v)^[d] (independentOutputS D Sc cutoff j.1 v) =
      ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
        outputLongExtraction D Sc cutoff p j.1 v
          (outputCorrectedLift D Sc cutoff p j v (d + n)
            (independentOutputS D Sc cutoff j.1 v n)) :=
  outputCoefficientRho_iterate_independentS D Sc cutoff p j v d

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d]
        (projection D Sc cutoff j.1 v (v ++ [j.1])
          (affineUnit D Sc cutoff (j.1 :: v) (v ++ [j.1]) (moveHom D Sc j.1 [] v)))) =
      SKM.zsign k (D.parity j.1) ^ v.count j.1 •
        ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          outputLongExtraction D Sc cutoff p j.1 v
            (outputCorrectedLift D Sc cutoff p j v (d + n)
              (independentOutputS D Sc cutoff j.1 v n)) :=
  outputLongExtraction_boundaryRho_move_independentS D Sc cutoff p j v d

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (q : ℕ) :
    outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[2 * q]
        (projection D Sc cutoff j.1 v (v ++ [j.1]) (move D Sc cutoff j.1 v))) =
      SKM.zsign k (D.parity j.1) ^ v.count j.1 •
        ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          Finsupp.single (2 * q + n) (independentOutputS D Sc cutoff j.1 v n) :=
  outputLongExtraction_boundaryRho_move_even D Sc cutoff p j v q

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (q : ℕ) :
    outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[2 * q + 1]
        (projection D Sc cutoff j.1 v (v ++ [j.1]) (move D Sc cutoff j.1 v))) =
      SKM.zsign k (D.parity j.1) ^ v.count j.1 •
        ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          (Finsupp.single (2 * q + n + 1) (independentOutputS D Sc cutoff j.1 v n) +
            Finsupp.single (2 * q + n) (outputDeltaCoefficient D Sc cutoff p j v
              (independentOutputS D Sc cutoff j.1 v n))) :=
  outputLongExtraction_boundaryRho_move_odd D Sc cutoff p j v q

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      appendProjection D Sc cutoff j.1 v (v ++ [j.1])
        (appendMovingPower D Sc cutoff j.1 v d ≫
          affineUnit D Sc cutoff _ _ (appendQPProduct D Sc j.1 v) ≫
          endpointELV D Sc cutoff j.1 v) -
      SKM.zsign k (D.parity j.1) ^ v.count j.1 •
        ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          pMap D Sc cutoff j.1 v (v ++ [j.1])
            (outputCorrectedLift D Sc cutoff p j v (d + n)
              (independentOutputS D Sc cutoff j.1 v n)) ∈
        chronologicalCrossingSpan D Sc cutoff j.1 v v :=
  reverseBoundary_sub_correctedS_mem D Sc cutoff p j v d

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ)
    (b : Old D Sc cutoff v v) :
    outputLongExtraction D Sc cutoff p j.1 v
      ((boundaryRho D Sc cutoff j v (v ++ [j.1]))^[d]
        (balancedForward D Sc cutoff p j.1 v (v ++ [j.1])
          (balancedTmul D Sc cutoff p j.1 (move D Sc cutoff j.1 v) b))) =
      SKM.zsign k (D.parity j.1) ^ v.count j.1 •
        ∑ n ∈ (independentOutputS D Sc cutoff j.1 v).support,
          outputLongExtraction D Sc cutoff p j.1 v
            (outputCorrectedLift D Sc cutoff p j v (d + n)
              (oldComp D Sc cutoff v v v b (independentOutputS D Sc cutoff j.1 v n))) :=
  outputLongExtraction_boundaryRho_move_balanced D Sc cutoff p j v d b

open Lean in
run_cmd do
  let env ← Lean.getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOutputSIterates
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  let mut count : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    logInfo m!"AUDIT {owner} {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Empty declaration inventory for {owner}"
  logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
