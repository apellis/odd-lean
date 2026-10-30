import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryLeading
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRowLeading
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (p : ZMod 2) (i : I) (hi : D.parity i = 0) (v : List I)
    (d m : ℕ) (b : Old D Sc cutoff v v)
    (hm : d + endpointQPDegree D cutoff i v < m + outputSDegree D i v) :
    evenPolynomialBoundary D Sc cutoff p i v (Finsupp.single d b) m = 0 :=
  evenPolynomialBoundary_single_above D Sc cutoff p i hi v d m b hm

example (p : ZMod 2) (i : I) (hi : D.parity i = 0) (v : List I)
    (d : ℕ) (b : Old D Sc cutoff v v)
    (hd : outputSDegree D i v ≤ d + endpointQPDegree D cutoff i v) :
    evenPolynomialBoundary D Sc cutoff p i v (Finsupp.single d b)
      (d + endpointQPDegree D cutoff i v - outputSDegree D i v) =
      (appendQPProductUnit D Sc i v : k) • oldTwist D Sc cutoff p v v b :=
  evenPolynomialBoundary_single_top D Sc cutoff p i hi v d b hd

example (p : ZMod 2) (i : I) (hi : D.parity i = 0) (v : List I)
    (d : ℕ) (b : Old D Sc cutoff v v)
    (hd : d + endpointQPDegree D cutoff i v < outputSDegree D i v) :
    evenPolynomialBoundary D Sc cutoff p i v (Finsupp.single d b) = 0 :=
  evenPolynomialBoundary_single_eq_zero D Sc cutoff p i hi v d b hd

example (p : ZMod 2) (i : I) (hi : D.parity i = 0) (v : List I)
    (d : ℕ) (b : Old D Sc cutoff v v)
    (hzero : endpointQPDegree D cutoff i v = outputSDegree D i v) :
    evenPolynomialBoundary D Sc cutoff p i v (Finsupp.single d b) d =
      evenBoundaryLeadingEquiv D Sc cutoff p i v b :=
  evenPolynomialBoundary_top D Sc cutoff p i hi v d d b (by omega)

example (p : ZMod 2) (i : I) (v : List I) (b : Old D Sc cutoff v v) :
    (evenBoundaryLeadingEquiv D Sc cutoff p i v).symm
      (evenBoundaryLeadingEquiv D Sc cutoff p i v b) = b :=
  (evenBoundaryLeadingEquiv D Sc cutoff p i v).symm_apply_apply b

example (i : I) (v : List I) :
    (endpointQPDegree D cutoff i v : ℤ) - outputSDegree D i v =
      (cutoff i : ℤ) - (v.map (fun j => D.h i (D.α j))).sum :=
  endpointQPDegree_sub_outputSDegree D cutoff i v

run_cmd do
  let env ← Lean.getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryPolynomial,
      `OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryRecurrence,
      `OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryLeading] do
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
