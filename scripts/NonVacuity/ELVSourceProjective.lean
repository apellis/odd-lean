import OddMath.QuiverHecke.CyclotomicAction.ELVSourceProjective
import Lean.Util.CollectAxioms

/-! Full-content finite projectivity, signed extraction, zero corners and literal
old idempotent polynomial rows. No finiteness assumption on the colour type. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (ν : List I) :
    Module.Projective (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K1 D Sc cutoff i ν) := inferInstance
example (i : I) (ν : List I) :
    Module.Finite (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K1 D Sc cutoff i ν) := inferInstance
example (i : I) (ν : List I) :
    Module.Projective (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K1Prime D Sc cutoff i ν) := inferInstance
example (i : I) (ν : List I) :
    Module.Finite (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K1Prime D Sc cutoff i ν) := inferInstance

example (i : I) :
    Module.Projective (Polynomial (ContentRing D Sc (fun _ => 0) []))ᵐᵒᵖ
      (K1 D Sc (fun _ => 0) i []) := inferInstance
example (i : I) :
    Module.Finite (Polynomial (ContentRing D Sc (fun _ => 0) []))ᵐᵒᵖ
      (K1Prime D Sc (fun _ => 0) i []) := inferInstance

example (i j : I) (hi : D.parity i = 1) (hj : D.parity j = 0) :
    centralDegree D i = 2 ∧ centralDegree D j = 1 := by
  simp [centralDegree, hi, hj]

example (i : I) (ν : List I) (z : K1 D Sc cutoff i ν) :
    (K1IdempotentEquiv D Sc cutoff i ν).symm (K1IdempotentEquiv D Sc cutoff i ν z) = z :=
  (K1IdempotentEquiv D Sc cutoff i ν).symm_apply_apply z
example (i : I) (ν : List I)
    (z : PolynomialIdempotentRows D Sc cutoff ν (centralDegree D i)) :
    K1PrimeIdempotentEquiv D Sc cutoff i ν ((K1PrimeIdempotentEquiv D Sc cutoff i ν).symm z) = z :=
  (K1PrimeIdempotentEquiv D Sc cutoff i ν).apply_symm_apply z

-- Full noncommutative polynomial action, not merely central scalars.
example (i : I) (ν : List I) (a : (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ)
    (z : K1 D Sc cutoff i ν) :
    K1IdempotentEquiv D Sc cutoff i ν (a • z) = a • K1IdempotentEquiv D Sc cutoff i ν z :=
  (K1IdempotentEquiv D Sc cutoff i ν).map_smul a z

-- Off-diagonal old action retains the prescribed source twist in reconstruction.
example (p : ZMod 2) (i : I) (u v t w : List I) (c : Old D Sc cutoff u v)
    (h : hom D Sc cutoff (i :: t) w) (b : Old D Sc cutoff v t) :
    sourcePull D Sc cutoff p i u v w c (pair D Sc cutoff p i h b) =
      pair D Sc cutoff p i h (oldComp D Sc cutoff u v t c b) :=
  sourcePull_pair D Sc cutoff p i c h b

example (p : ZMod 2) (i : I) (ν : List I) (z : SourceEndpointPolynomial D Sc cutoff p i ν) :
    sourceEndpointRetraction D Sc cutoff p i ν (sourceEndpointSection D Sc cutoff p i ν z) = z :=
  sourceEndpointRetraction_section D Sc cutoff p i ν z

example (p q : ZMod 2) (i : I) (ν : List I) (z : SourceEndpointPolynomial D Sc cutoff p i ν) :
    (sourceEndpointTwistEquiv D Sc cutoff p q i ν).symm
      (sourceEndpointTwistEquiv D Sc cutoff p q i ν z) = z :=
  (sourceEndpointTwistEquiv D Sc cutoff p q i ν).symm_apply_apply z

example (i : I) (ν : List I) (z : K1Prime D Sc cutoff i ν) :
    ∀ q, ∃ b : Polynomial (ContentRing D Sc cutoff ν),
      ((K1PrimeIdempotentEquiv D Sc cutoff i ν z).val q).unop =
        Polynomial.C (FiniteHomMatrix.idem (obj := contentObject D Sc cutoff ν) q.1.1) * b :=
  (polynomialIdempotentRows_mem_iff D Sc cutoff ν (centralDegree D i) _).mp
    (K1PrimeIdempotentEquiv D Sc cutoff i ν z).property

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVSourceRows,
      `OddMath.QuiverHecke.CyclotomicAction.ELVSourceRowsEquivalence,
      `OddMath.QuiverHecke.CyclotomicAction.ELVSourcePolynomialRows,
      `OddMath.QuiverHecke.CyclotomicAction.ELVPolynomialIdempotents,
      `OddMath.QuiverHecke.CyclotomicAction.ELVSourceProjective] do
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
