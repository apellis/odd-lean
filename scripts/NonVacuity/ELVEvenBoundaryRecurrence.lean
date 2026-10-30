import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryRecurrence
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (p : ZMod 2) (i : I) (hi : D.parity i = 0) (v : List I)
    (c : Old D Sc cutoff v v) (f : ℕ →₀ Old D Sc cutoff v v) :
    evenPolynomialBoundary D Sc cutoff p i v
      (outputCoefficientRightAction D Sc cutoff i p v c f) =
    outputCoefficientRightAction D Sc cutoff i 0 v c
      (evenPolynomialBoundary D Sc cutoff p i v f) :=
  evenPolynomialBoundary_rightAction_even D Sc cutoff p i hi v c f

example (p : ZMod 2) (i : I) (hi : D.parity i = 0) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) (m : ℕ) :
    evenPolynomialBoundary D Sc cutoff p i v (appendOutputShift D Sc cutoff v v f) (m + 1) =
      evenPolynomialBoundary D Sc cutoff p i v f m :=
  evenPolynomialBoundary_shift_high D Sc cutoff p i hi v f m

example (p : ZMod 2) (i : I) (hi : D.parity i = 0) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    outputLongExtraction D Sc cutoff p i v
      (movingPowerTarget D Sc cutoff i v (v ++ [i]) 1 (by simp [hi]) z) =
    appendOutputShift D Sc cutoff v v (outputLongExtraction D Sc cutoff p i v z) :=
  outputLongExtraction_evenDot D Sc cutoff p i hi v z

run_cmd do
  let env ← Lean.getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryPolynomial,
      `OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryRecurrence] do
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
