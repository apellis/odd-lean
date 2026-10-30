import OddMath.QuiverHecke.CyclotomicAction.ELVIndependentSBoundaryDivision
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (c : Old D Sc cutoff v v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputPolynomialBoundary D Sc cutoff p j v
      (outputCoefficientRightAction D Sc cutoff j.1
        (p + D.parity j.1 * wordSumParity D v) v c f) =
    outputCoefficientRightAction D Sc cutoff j.1 0 v c
      (outputPolynomialBoundary D Sc cutoff p j v f) :=
  outputPolynomialBoundary_rightAction D Sc cutoff p j v c f

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (n : ℕ)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputPolynomialBoundary D Sc cutoff p j v
      (Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
        (independentOutputS D Sc cutoff j.1 v n)) f) =
    Finsupp.mapRange.linearMap ((oldComp D Sc cutoff v v v).flip
      (independentOutputS D Sc cutoff j.1 v n))
      (outputPolynomialBoundary D Sc cutoff p j v f) :=
  outputPolynomialBoundary_independentS_postcomp D Sc cutoff p j v n f

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) :
    let w := outputLongExtraction D Sc cutoff p j.1 v
      (outputCorrectedLift D Sc cutoff p j v d ((ideal D Sc cutoff v v).mkQ (𝟙 _)))
    let sigma := SKM.zsign k (D.parity j.1) ^ v.count j.1
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      inputCoefficientShift D Sc cutoff j.1 v d
        (orderedQPOutputCoefficients D Sc cutoff j.1 v (List.range v.length)
          (endpointOutputCoefficients D Sc cutoff j.1 v)) =
      independentSRightProduct D Sc cutoff j.1 v (sigma • outputBoundaryPhi D Sc cutoff p j v d) +
        sigma • independentSBoundaryRemainder D Sc cutoff p j v w :=
  independentS_boundary_division D Sc cutoff p j v d

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    (independentSBoundaryRemainder D Sc cutoff p j v f).support ⊆
      Finset.range (outputSDegree D j.1 v) :=
  independentSBoundaryRemainder_support D Sc cutoff p j v f

example (j : {j : I // D.parity j = 1})
    (v : List I) (f g r s : ℕ →₀ Old D Sc cutoff v v)
    (hr : r.support ⊆ Finset.range (outputSDegree D j.1 v))
    (hs : s.support ⊆ Finset.range (outputSDegree D j.1 v))
    (h : independentSRightProduct D Sc cutoff j.1 v f + r =
      independentSRightProduct D Sc cutoff j.1 v g + s) : f = g ∧ r = s :=
  independentS_division_unique D Sc cutoff j v f g r s hr hs h

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ)
    (hd : outputSDegree D j.1 v ≤ d + endpointQPDegree D cutoff j.1 v) :
    (SKM.zsign k (D.parity j.1) ^ v.count j.1 • outputBoundaryPhi D Sc cutoff p j v d)
      (d + endpointQPDegree D cutoff j.1 v - outputSDegree D j.1 v) =
    sign k ((cutoff j.1 • D.parity j.1) * (D.parity j.1 * wordSumParity D v)) •
      ((appendQPProductUnit D Sc j.1 v : k) • (ideal D Sc cutoff v v).mkQ (𝟙 _)) :=
  outputBoundaryPhi_signed_top D Sc cutoff p j v d hd

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ)
    (hd : d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v) :
    outputBoundaryPhi D Sc cutoff p j v d = 0 :=
  outputBoundaryPhi_eq_zero_of_negative D Sc cutoff p j v d hd

run_cmd do
  let env ← Lean.getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryCoefficientAction,
      `OddMath.QuiverHecke.CyclotomicAction.ELVIndependentSBoundaryDivision] do
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
