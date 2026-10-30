import OddMath.QuiverHecke.CyclotomicAction.ELVContentModule
import Lean.Util.CollectAxioms

/-! Ordinary polynomial module consumers, including arbitrary colour types,
empty content, zero cutoff, full old off-diagonal arrows and the two twists. -/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (ν : List I) :
    Module (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K0 D Sc cutoff i ν) := inferInstance
example (i : I) (ν : List I) :
    Module (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K1 D Sc cutoff i ν) := inferInstance
example (i : I) (ν : List I) :
    Module (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K1Prime D Sc cutoff i ν) := inferInstance
example (i : I) :
    Module (Polynomial (ContentRing D Sc cutoff []))ᵐᵒᵖ (K1 D Sc cutoff i []) := inferInstance

example (i : I) (ν : List I) (b : (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ)
    (z : K1 D Sc cutoff i ν) :
    pPolynomial D Sc cutoff i ν (b • z) = b • pPolynomial D Sc cutoff i ν z :=
  (pPolynomial D Sc cutoff i ν).map_smul b z

example (i : I) (ν : List I) (b : (Polynomial (ContentRing D Sc (fun _ => 0) ν))ᵐᵒᵖ)
    (z : K1 D Sc (fun _ => 0) i ν) :
    pPolynomial D Sc (fun _ => 0) i ν (b • z) = b • pPolynomial D Sc (fun _ => 0) i ν z :=
  (pPolynomial D Sc (fun _ => 0) i ν).map_smul b z

example (i : I) (ν : List I) : Function.Injective (pPolynomial D Sc cutoff i ν) :=
  pPolynomial_injective D Sc cutoff i ν

example (i : I) (u v w : List I) (c : Old D Sc cutoff u v)
    (z : Target D Sc cutoff i v w) :
    pMap D Sc cutoff i u w (sourcePull D Sc cutoff (appendQ D cutoff i u) i u v w c z) =
      appendPull D Sc cutoff i u v w c (pMap D Sc cutoff i v w z) :=
  pMap_sourcePull D Sc cutoff i c z

example (p : ZMod 2) (i : I) (ν : List I)
    (z : SourceContent D Sc cutoff p i ν) :
    (sourceContentCoordinateEquiv D Sc cutoff p i ν).symm
      (sourceContentCoordinateEquiv D Sc cutoff p i ν z) = z :=
  (sourceContentCoordinateEquiv D Sc cutoff p i ν).symm_apply_apply z

example (i : I) (hi : D.parity i = 1) (ν : List I) :
    appendQ D (fun _ => 1) i ν = D.parity i * wordSumParity D ν + 1 := by
  simp [ELVOld.appendQ, hi]

example (p : ZMod 2) (i : I) (u v w : List I) (z : Target D Sc cutoff i v w) :
    sourcePull D Sc cutoff p i u v w 0 z = 0 := by simp

-- The polynomial construction also works over an explicit noncommutative ring.
example : Module (Polynomial (AddMonoid.End (ℤ × ℤ)))
    (CentralPolynomialModule (LinearMap.id : AddMonoid.End (ℤ × ℤ) →ₗ[AddMonoid.End (ℤ × ℤ)]
      AddMonoid.End (ℤ × ℤ))) := inferInstance

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.FiniteHomMatrixRightModule,
      `OddMath.QuiverHecke.CyclotomicAction.CentralPolynomialModule,
      `OddMath.QuiverHecke.CyclotomicAction.CentralPolynomialRightModule,
      `OddMath.QuiverHecke.CyclotomicAction.ELVOldCategory,
      `OddMath.QuiverHecke.CyclotomicAction.ELVEndpointPresheaf,
      `OddMath.QuiverHecke.CyclotomicAction.ELVContentModule] do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Missing module {owner}"
    let mut count : Nat := 0
    for name in env.header.moduleData[idx]!.constNames do
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      count := count + 1
    if count == 0 then throwError "Empty declaration inventory for {owner}"
    logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
