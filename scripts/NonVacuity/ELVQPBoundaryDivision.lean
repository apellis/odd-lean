import OddMath.QuiverHecke.CyclotomicAction.ELVQPBoundaryDivision
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v w : List I) (z : AppendTarget D Sc cutoff i v w) :
    ∃ (g : hom D Sc cutoff (v ++ [i]) w) (r : AppendTarget D Sc cutoff i v w),
      z = appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v ≫ g) + r ∧
      ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w r).support,
        t.1.1 < endpointQPDegree D cutoff i v :=
  endpointQP_division D Sc cutoff i v w z

example (i : I) (v w : List I) (h : hom D Sc cutoff (v ++ [i]) w)
    (q : AppendIdx.Tail i v w)
    (hm : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, t.1.1 ≤ q.1.1) :
    appendOldCoordinate D Sc cutoff 0 (q.representative.shift (endpointQPDegree D cutoff i v))
      (appendProjection D Sc cutoff i v w
        (normalizedEndpointQPNumerator D Sc cutoff i v ≫ h)) =
      oldTwist D Sc cutoff (cutoff i • D.parity i) v q.representative.oldTarget
        ((appendOldCoordinateEquiv D Sc cutoff 0 i v w
          (appendProjection D Sc cutoff i v w h)) q) :=
  normalizedEndpointQPNumerator_top D Sc cutoff i v w h q hm

#print axioms endpointQP_top
#print axioms endpointQP_above
#print axioms endpointQP_single_division
#print axioms endpointQP_division
#print axioms normalizedEndpointQPNumerator_top

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVQPBoundaryDivision] do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Module was not imported: {owner}"
    let mut count : Nat := 0
    for name in env.header.moduleData[idx]!.constNames do
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      count := count + 1
    if count == 0 then throwError "Empty declaration inventory: {owner}"
    logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
