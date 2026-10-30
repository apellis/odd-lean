import OddMath.QuiverHecke.CyclotomicAction.ELVChronologicalKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVShortTailSpan
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputMoveComparison
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
example (p : ZMod 2) (i : I) (v : List I) :
    chronologicalShortSpan D Sc cutoff i v v ≤
      LinearMap.ker (outputLongExtraction D Sc cutoff p i v) :=
  chronologicalShortSpan_le_ker_outputLongExtraction D Sc cutoff p i v
example (i : I) (v t : List I) (x : PrependIdx i v (t ++ [i]))
    (hx : x.1.2.2.2 ≠ longPrependShuffle v.length)
    (r : hom D Sc cutoff v x.oldTarget) :
    projection D Sc cutoff i v (t ++ [i])
      (insert D Sc cutoff i v x.oldTarget r ≫
        affineUnit D Sc cutoff _ _ (prependTail D Sc x)) ∈
      chronologicalShortSpan D Sc cutoff i v t :=
  prepend_short_mem D Sc cutoff i v t x hx r
example (p : ZMod 2) (i : I) (v : List I) :
    LinearMap.ker (outputLongExtraction D Sc cutoff p i v) =
      chronologicalShortSpan D Sc cutoff i v v :=
  ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v

open scoped TensorProduct
example (p : ZMod 2) (i : I) (v : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    projection D Sc cutoff i v (v ++ [i]) (a ⊗ₜ[k] moveHom D Sc i [] v) -
    projection D Sc cutoff i v (v ++ [i])
      (a ⊗ₜ[k] (leadingMoveEndpointPolynomial D Sc i [] v ≫
        cl D Sc _ _ (cw (leadingMoveWord [] v)) (leadingMoveWord_sChain i [] v))) ∈
      chronologicalShortSpan D Sc cutoff i v v :=
  move_sub_endpointPolynomial_mem_chronologicalShortSpan D Sc cutoff p i v a

open Lean in
run_cmd do
  let env ← Lean.getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.SmallerTailNormalization,
      `OddMath.QuiverHecke.CyclotomicAction.ELVChronologicalKernel,
      `OddMath.QuiverHecke.CyclotomicAction.ELVShortTailSpan,
      `OddMath.QuiverHecke.CyclotomicAction.ELVOutputKernel,
      `OddMath.QuiverHecke.CyclotomicAction.ELVOutputMoveComparison] do
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
