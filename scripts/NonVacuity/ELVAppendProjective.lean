import OddMath.QuiverHecke.CyclotomicAction.ELVAppendSupport
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
    Module.Projective (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K0 D Sc cutoff i ν) := inferInstance
example (i : I) (ν : List I) :
    Module.Finite (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (K0 D Sc cutoff i ν) := inferInstance

example (i j : I) :
    Module.Projective (Polynomial (ContentRing D Sc (fun _ => 0) [j]))ᵐᵒᵖ
      (K0 D Sc (fun _ => 0) i [j]) := inferInstance

example (i : I) :
    Module.Projective (Polynomial (ContentRing D Sc (fun _ => 0) []))ᵐᵒᵖ
      (K0 D Sc (fun _ => 0) i []) := inferInstance
example (i : I) :
    Module.Finite (Polynomial (ContentRing D Sc (fun _ => 0) []))ᵐᵒᵖ
      (K0 D Sc (fun _ => 0) i []) := inferInstance

example (i j : I) (hi : D.parity i = 1) (hj : D.parity j = 0) :
    centralDegree D i = 2 ∧ centralDegree D j = 1 := by
  simp [centralDegree, hi, hj]

example (i : I) (ν : List I) (z : K0 D Sc cutoff i ν) :
    (K0IdempotentEquiv D Sc cutoff i ν).symm (K0IdempotentEquiv D Sc cutoff i ν z) = z :=
  (K0IdempotentEquiv D Sc cutoff i ν).symm_apply_apply z
example (i : I) (ν : List I)
    (z : AppendPolynomialIdempotentRows D Sc cutoff i ν (centralDegree D i)) :
    K0IdempotentEquiv D Sc cutoff i ν ((K0IdempotentEquiv D Sc cutoff i ν).symm z) = z :=
  (K0IdempotentEquiv D Sc cutoff i ν).apply_symm_apply z

-- Full noncommutative polynomial action, not merely central scalars.
example (i : I) (ν : List I) (a : (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ)
    (z : K0 D Sc cutoff i ν) :
    K0IdempotentEquiv D Sc cutoff i ν (a • z) = a • K0IdempotentEquiv D Sc cutoff i ν z :=
  (K0IdempotentEquiv D Sc cutoff i ν).map_smul a z

-- Off-diagonal old action uses the full signed coefficient quotient.
example (i : I) (u v t w : List I) (c : Old D Sc cutoff u v)
    (h : hom D Sc cutoff (t ++ [i]) w) (b : Old D Sc cutoff v t) :
    appendPull D Sc cutoff i u v w c (appendPair D Sc cutoff 0 i h b) =
      appendPair D Sc cutoff 0 i h (oldComp D Sc cutoff u v t c b) :=
  appendPull_pair D Sc cutoff i c h b

example (i : I) (ν : List I) (z : AppendEndpointPolynomial D Sc cutoff i ν) :
    appendEndpointRetraction D Sc cutoff i ν (appendEndpointSection D Sc cutoff i ν z) = z :=
  appendEndpointRetraction_section D Sc cutoff i ν z

example (i : I) (ν : List I) (z : K0 D Sc cutoff i ν) :
    ∀ q, ∃ b : Polynomial (ContentRing D Sc cutoff ν),
      ((K0IdempotentEquiv D Sc cutoff i ν z).val q).unop =
        Polynomial.C (FiniteHomMatrix.idem (obj := contentObject D Sc cutoff ν) q.1.1) * b :=
  (appendPolynomialIdempotentRows_mem_iff D Sc cutoff i ν (centralDegree D i) _).mp
    (K0IdempotentEquiv D Sc cutoff i ν z).property

example (i : I) (ν : List I) (z : AppendContent D Sc cutoff i ν) :
    ∃ N, appendDecode D Sc cutoff i ν z ∈ appendRowsBelow D Sc cutoff i ν N :=
  appendRows_bounded D Sc cutoff i ν _

example (i j : I) (hi : D.parity i = 1) (hj : D.parity j = 0)
    (z : AppendContent D Sc cutoff i [i, j]) :
    appendDecode D Sc cutoff i [i, j] (appendContentCentral D Sc cutoff i [i, j] z) =
      appendRowsShift D Sc cutoff i [i, j] 2 (appendDecode D Sc cutoff i [i, j] z) ∧
      centralDegree D j = 1 := by
  constructor
  · simpa only [centralDegree, hi, one_ne_zero, ↓reduceIte] using
      appendDecode_central D Sc cutoff i [i, j] z
  · simp [centralDegree, hj]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVAppendCoordinates,
      `OddMath.QuiverHecke.CyclotomicAction.ELVAppendOldExtraction,
      `OddMath.QuiverHecke.CyclotomicAction.ELVAppendCrossTail,
      `OddMath.QuiverHecke.CyclotomicAction.ELVAppendDescent,
      `OddMath.QuiverHecke.CyclotomicAction.ELVAppendRows,
      `OddMath.QuiverHecke.CyclotomicAction.ELVAppendRowsEquivalence,
      `OddMath.QuiverHecke.CyclotomicAction.ELVAppendRowsShift,
      `OddMath.QuiverHecke.CyclotomicAction.ELVAppendPolynomialRows,
      `OddMath.QuiverHecke.CyclotomicAction.ELVAppendPolynomialIdempotents,
      `OddMath.QuiverHecke.CyclotomicAction.ELVAppendProjective,
      `OddMath.QuiverHecke.CyclotomicAction.ELVAppendSupport] do
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
