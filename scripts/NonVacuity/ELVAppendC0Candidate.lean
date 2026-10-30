import OddMath.QuiverHecke.CyclotomicAction.ELVAppendC0Candidate
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    appendC0Candidate D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) = f :=
  appendC0Candidate_embedding D Sc cutoff i v t f

example (i : I) (v t : List I) :
    Function.Injective (appendOutputEmbedding D Sc cutoff i v t) :=
  appendOutputEmbedding_injective D Sc cutoff i v t

example (i : I) (v s t : List I)
    (x : AppendIdx i v (t ++ [i])) (e : x.oldTarget = s ++ [i])
    (L : List PG)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross s.length :: L)
    (hf : Fits (s ++ [i]).length L)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (r : hom D Sc cutoff v x.oldTarget) :
    appendC0Candidate D Sc cutoff i v t
      (appendCrossingClass D Sc cutoff i v s t (e ▸ r)
        (appendMovingPower D Sc cutoff i s x.1.1 ≫
          affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))) = 0 :=
  appendC0Candidate_canonical_crossing D Sc cutoff i v s t x e L hw hf h r

open Lean in
run_cmd do
  let env ← Lean.getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVAppendC0Candidate
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
