import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryPolynomial
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    appendC0 D Sc cutoff i v v (pMap D Sc cutoff i v (v ++ [i]) z) =
      evenPolynomialBoundary D Sc cutoff p i v (outputLongExtraction D Sc cutoff p i v z) :=
  evenPolynomialBoundary_factor D Sc cutoff p i v z

example (p : ZMod 2) (i : I) (v : List I) (d : ℕ) (b : Old D Sc cutoff v v) :
    evenPolynomialBoundary D Sc cutoff p i v (Finsupp.single d b) =
      appendC0 D Sc cutoff i v v
        (pMap D Sc cutoff i v (v ++ [i]) (outputLongLift D Sc cutoff p i v d b)) :=
  evenPolynomialBoundary_single D Sc cutoff p i v d b

example (p : ZMod 2) (i : I) (hi : D.parity i = 0) (v : List I) (d : ℕ) :
    evenPolynomialBoundary D Sc cutoff p i v
      (outputLongExtraction D Sc cutoff p i v
        ((movingPowerTarget D Sc cutoff i v (v ++ [i]) 1 (by simp [hi]))^[d]
          (projection D Sc cutoff i v (v ++ [i]) (move D Sc cutoff i v)))) =
      inputCoefficientShift D Sc cutoff i v d
        (orderedQPOutputCoefficients D Sc cutoff i v (List.range v.length)
          (endpointOutputCoefficients D Sc cutoff i v)) :=
  evenPolynomialBoundary_reverseNumerator D Sc cutoff p i hi v d

example (p : ZMod 2) (i : I) (hi : D.parity i = 0) (v : List I) :
    evenPolynomialBoundary D Sc cutoff p i v (independentOutputS D Sc cutoff i v) =
      orderedQPOutputCoefficients D Sc cutoff i v (List.range v.length)
        (endpointOutputCoefficients D Sc cutoff i v) :=
  evenPolynomialBoundary_independentS D Sc cutoff p i hi v

run_cmd do
  let env ← Lean.getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryPolynomial
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
