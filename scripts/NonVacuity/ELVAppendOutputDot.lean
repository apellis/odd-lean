import OddMath.QuiverHecke.CyclotomicAction.ELVAppendOutputDot
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v t : List I) (f : ℕ →₀ hom D Sc cutoff v t) :
    appendOutputEmbedding D Sc cutoff i v t
      (Finsupp.mapRange.linearMap (ideal D Sc cutoff v t).mkQ f) =
    appendProjection D Sc cutoff i v (t ++ [i]) (appendOutputPolynomial D Sc cutoff i v t f) :=
  appendOutputEmbedding_map D Sc cutoff i v t f

example (i : I) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    appendOutputDot D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) =
      appendOutputEmbedding D Sc cutoff i v t (appendOutputShift D Sc cutoff v t f) :=
  appendOutputDot_embedding D Sc cutoff i v t f

example (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendOutputDot D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g) =
      SKM.zsign k (D.parity i * D.parity i) •
        appendCrossingClass D Sc cutoff i v s t
          (r ≫ appendMovingPower D Sc cutoff i s 1) (twist k (D.parity i) g) -
      SKM.zsign k (D.parity i * D.parity i) •
        appendOutputEmbedding D Sc cutoff i v t
          (Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ (r ≫ twist k (D.parity i) g))) :=
  appendOutputDot_crossingClass D Sc cutoff i v s t r g

example (i : I) (hi : D.parity i = 1) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendOutputDot D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g) =
      -appendCrossingClass D Sc cutoff i v s t
        (r ≫ appendMovingPower D Sc cutoff i s 1) (twist k 1 g) +
      appendOutputEmbedding D Sc cutoff i v t
        (Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ (r ≫ twist k 1 g))) :=
  appendOutputDot_crossingClass_odd D Sc cutoff i hi v s t r g

open Lean in
run_cmd do
  let env ← Lean.getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVAppendOutputDot
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
  if count == 0 then throwError "Empty declaration inventory"
  logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
