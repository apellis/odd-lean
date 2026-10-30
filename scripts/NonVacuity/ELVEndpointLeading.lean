import OddMath.QuiverHecke.CyclotomicAction.ELVEndpointLeading
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) (q : AppendIdx.Tail i v w)
    (hmax : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, t.1.1 ≤ q.1.1) :
    appendOldCoordinate D Sc cutoff 0 (q.representative.shift (cutoff i))
      (appendProjection D Sc cutoff i v w (endpointELV D Sc cutoff i v ≫ h)) =
    oldTwist D Sc cutoff (cutoff i • D.parity i) v q.representative.oldTarget
      ((appendOldCoordinateEquiv D Sc cutoff 0 i v w
        (appendProjection D Sc cutoff i v w h)) q) :=
  endpointELV_top D Sc cutoff i v w h q hmax

example (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) (x : AppendIdx i v w)
    (hbound : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, cutoff i + t.1.1 < x.1.1) :
    appendOldCoordinate D Sc cutoff 0 x
      (appendProjection D Sc cutoff i v w (endpointELV D Sc cutoff i v ≫ h)) = 0 :=
  endpointELV_above D Sc cutoff i v w h x hbound

example (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w (endpointELV D Sc cutoff i v ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 :=
  appendProjection_endpointELV_regular D Sc cutoff i v w h hh

example (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
        endpointELV D Sc cutoff i v ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 :=
  appendProjection_qp_endpointELV_regular D Sc cutoff i v w h hh

#print axioms endpointELV_top
#print axioms appendProjection_qp_endpointELV_regular

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[
    `OddMath.QuiverHecke.CyclotomicAction.ELVAppendSignedMovingSupport,
    `OddMath.QuiverHecke.CyclotomicAction.ELVEndpointLeading]
  for owner in owners do
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
