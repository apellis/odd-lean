import OddMath.QuiverHecke.CyclotomicAction.ELVOutputSComparison
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
example (i : I) (v : List I) (n : ℕ) :
    independentOutputS D Sc cutoff i v n =
      SKM.zsign k (D.parity i) ^ v.count i •
        ∑ c : MoveChoices v,
          if sourceMovingDegree (leadingSourceDots D i 0 0 v c) = n then
            leadingMoveCoeff D (k := k) i v c •
              (ideal D Sc cutoff v v).mkQ (leadingSourceOldArrow D Sc cutoff i v c)
          else 0 :=
  independentOutputS_apply D Sc cutoff i v n

example (p : ZMod 2) (i : I) (v : List I) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (affineUnit D Sc cutoff (i :: v) (v ++ [i])
          ((∑ c : MoveChoices v, leadingMoveCoeff D (k := k) i v c •
            endpointDotMonomial D Sc (i :: v) (leadingSourceDots D i 0 0 v c)) ≫
            OutputOldComposite.bareU D Sc i v))) =
      orderedOutputCoefficients D Sc cutoff i v :=
  outputLongExtraction_source_expansion D Sc cutoff p i v

example (p : ZMod 2) (i : I) (v : List I) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (affineUnit D Sc cutoff (i :: v) (v ++ [i])
          (leadingMoveSquareProduct D Sc i [] v ≫ OutputOldComposite.bareU D Sc i v))) =
      independentOutputS D Sc cutoff i v :=
  outputLongExtraction_squareProduct D Sc cutoff p i v

example (p : ZMod 2) (i : I) (v : List I) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (affineUnit D Sc cutoff (i :: v) (v ++ [i]) (moveHom D Sc i [] v))) =
      SKM.zsign k (D.parity i) ^ v.count i • independentOutputS D Sc cutoff i v :=
  outputLongExtraction_move_independentS D Sc cutoff p i v

example (p : ZMod 2) (i : I) (v : List I)
    (b : Old D Sc cutoff v v) (n : ℕ) :
    outputLongCoordinate D Sc cutoff p i v n
      (balancedForward D Sc cutoff p i v (v ++ [i])
        (balancedTmul D Sc cutoff p i
          (affineUnit D Sc cutoff (i :: v) (v ++ [i]) (moveHom D Sc i [] v)) b)) =
      oldComp D Sc cutoff v v v b
        (SKM.zsign k (D.parity i) ^ v.count i • independentOutputS D Sc cutoff i v n) :=
  outputLongCoordinate_move_independentS_balanced D Sc cutoff p i v b n

open Lean in
run_cmd do
  let env ← Lean.getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOutputSComparison
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
