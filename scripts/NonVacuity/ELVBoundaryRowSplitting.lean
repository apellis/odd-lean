import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRowSplitting
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : OddMath.SKM.Datum I X) (Sc : OddMath.SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v : List I) :
    (endpointQPDegree D cutoff i v : ℤ) - outputSDegree D i v =
      (cutoff i : ℤ) - (v.map (fun j => D.h i (D.α j))).sum :=
  endpointQPDegree_sub_outputSDegree D cutoff i v

example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (d n : ℕ) (c : Old D Sc cutoff v v)
    (hn : n + outputSDegree D j.1 v = d + endpointQPDegree D cutoff j.1 v) :
    outputPolynomialBoundary D Sc cutoff p j v
      (outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v d c)) n =
        outputBoundaryLeadingEquiv D Sc cutoff p j v n c :=
  outputBoundary_corrected_top D Sc cutoff p j v d n c hn

example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v)
    (x : (ℕ →₀ Old D Sc cutoff v v) × boundaryRowWindow D Sc cutoff j v) :
    (boundaryPositiveEquiv D Sc cutoff p j v h).symm
      (outputPolynomialBoundary D Sc cutoff p j v x.1 + x.2) = x := by
  rw [← boundaryPositiveEquiv_apply D Sc cutoff p j v h x]
  exact LinearEquiv.symm_apply_apply _ _

example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    boundaryPositiveEquiv D Sc cutoff p j v h
      ((boundaryPositiveEquiv D Sc cutoff p j v h).symm f) = f :=
  LinearEquiv.apply_symm_apply _ _

example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    ((boundaryNegativeEquiv D Sc cutoff p j v h).symm f).2 =
      outputPolynomialBoundary D Sc cutoff p j v f :=
  boundaryNegativeEquiv_symm_snd D Sc cutoff p j v h f

example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (x : boundaryKernelWindow D Sc cutoff j v × (ℕ →₀ Old D Sc cutoff v v)) :
    (boundaryNegativeEquiv D Sc cutoff p j v h).symm
      (outputCorrectedCoordinateEquiv D Sc cutoff p j v x.1 + boundaryRowSection D Sc cutoff p j v x.2) = x := by
  rw [← boundaryNegativeEquiv_apply D Sc cutoff p j v h x]
  exact LinearEquiv.symm_apply_apply _ _

example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    boundaryNegativeEquiv D Sc cutoff p j v h
      ((boundaryNegativeEquiv D Sc cutoff p j v h).symm f) = f :=
  LinearEquiv.apply_symm_apply _ _

example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    ((ℕ →₀ Old D Sc cutoff v v) ⧸ LinearMap.range (outputPolynomialBoundary D Sc cutoff p j v)) ≃ₗ[k]
      boundaryRowWindow D Sc cutoff j v := boundaryPositiveCokernelEquiv D Sc cutoff p j v h

example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    boundaryKernelWindow D Sc cutoff j v ≃ₗ[k]
      LinearMap.ker (outputPolynomialBoundary D Sc cutoff p j v) :=
  boundaryKernelEquiv D Sc cutoff p j v

example (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v) :
    Function.Bijective (outputPolynomialBoundary D Sc cutoff p j v) :=
  ⟨outputPolynomialBoundary_injective D Sc cutoff p j v h.ge,
    outputPolynomialBoundary_surjective D Sc cutoff p j v h.le⟩

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRowLeading,
    `OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRowDivision,
    `OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRowSplitting]
  for owner in owners do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited ALL {names.size} declarations in {owner}, including private/generated"
