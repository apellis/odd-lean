import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundarySplitting
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRowLeading
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

example (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I)
    (d n : ℕ) (c : Old D Sc cutoff v v)
    (hn : n + outputSDegree D j.1 v = d + endpointQPDegree D cutoff j.1 v) :
    evenPolynomialBoundary D Sc cutoff p j.1 v
      (Finsupp.single d c) n =
        evenBoundaryLeadingEquiv D Sc cutoff p j.1 v c :=
  evenPolynomialBoundary_top D Sc cutoff p j.1 j.2 v d n c hn

example (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v)
    (x : (ℕ →₀ Old D Sc cutoff v v) × evenBoundaryRowWindow D Sc cutoff j v) :
    (evenBoundaryPositiveEquiv D Sc cutoff p j v h).symm
      (evenPolynomialBoundary D Sc cutoff p j.1 v x.1 + x.2) = x := by
  rw [← evenBoundaryPositiveEquiv_apply D Sc cutoff p j v h x]
  exact LinearEquiv.symm_apply_apply _ _

example (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    evenBoundaryPositiveEquiv D Sc cutoff p j v h
      ((evenBoundaryPositiveEquiv D Sc cutoff p j v h).symm f) = f :=
  LinearEquiv.apply_symm_apply _ _

example (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    ((evenBoundaryNegativeEquiv D Sc cutoff p j v h).symm f).2 =
      evenPolynomialBoundary D Sc cutoff p j.1 v f :=
  evenBoundaryNegativeEquiv_symm_snd D Sc cutoff p j v h f

example (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (x : evenBoundaryKernelWindow D Sc cutoff j v × (ℕ →₀ Old D Sc cutoff v v)) :
    (evenBoundaryNegativeEquiv D Sc cutoff p j v h).symm
      ((x.1 : ℕ →₀ Old D Sc cutoff v v) + evenBoundaryRowSection D Sc cutoff p j v x.2) = x := by
  rw [← evenBoundaryNegativeEquiv_apply D Sc cutoff p j v h x]
  exact LinearEquiv.symm_apply_apply _ _

example (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    evenBoundaryNegativeEquiv D Sc cutoff p j v h
      ((evenBoundaryNegativeEquiv D Sc cutoff p j v h).symm f) = f :=
  LinearEquiv.apply_symm_apply _ _

example (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    ((ℕ →₀ Old D Sc cutoff v v) ⧸ LinearMap.range (evenPolynomialBoundary D Sc cutoff p j.1 v)) ≃ₗ[k]
      evenBoundaryRowWindow D Sc cutoff j v := evenBoundaryPositiveCokernelEquiv D Sc cutoff p j v h

example (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I) :
    evenBoundaryKernelWindow D Sc cutoff j v ≃ₗ[k]
      LinearMap.ker (evenPolynomialBoundary D Sc cutoff p j.1 v) :=
  evenBoundaryKernelEquiv D Sc cutoff p j v

example (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v) :
    Function.Bijective (evenPolynomialBoundary D Sc cutoff p j.1 v) :=
  ⟨evenPolynomialBoundary_injective D Sc cutoff p j v h.ge,
    evenPolynomialBoundary_surjective D Sc cutoff p j v h.le⟩

example (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I)
    (x : evenBoundaryRowHigh D Sc cutoff j v × evenBoundaryRowWindow D Sc cutoff j v) :
    (evenBoundaryRowDivisionEquiv D Sc cutoff p j v).symm
      (evenPolynomialBoundary D Sc cutoff p j.1 v x.1 + x.2) = x := by
  rw [← evenBoundaryRowDivisionEquiv_apply D Sc cutoff p j v x]
  exact LinearEquiv.symm_apply_apply _ _

example (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    evenBoundaryRowDivisionEquiv D Sc cutoff p j v
      ((evenBoundaryRowDivisionEquiv D Sc cutoff p j v).symm f) = f :=
  LinearEquiv.apply_symm_apply _ _

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[`OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryPolynomial,
    `OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryRecurrence,
    `OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryLeading,
    `OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryDivision,
    `OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundarySplitting]
  for owner in owners do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owner {owner}"
    for name in names do
      for ax in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited ALL {names.size} declarations in {owner}, including private/generated"
