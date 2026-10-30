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

theorem c0ConsumerRecovery (i : I) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    appendC0 D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) = f :=
  appendC0_embedding D Sc cutoff i v t f

theorem c0ConsumerFullCrossing (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendC0 D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g) = 0 :=
  appendC0_crossing D Sc cutoff i v s t r g

theorem c0ConsumerKernel (i : I) (v t : List I) :
    LinearMap.ker (appendC0 D Sc cutoff i v t) = appendCrossingSpan D Sc cutoff i v t :=
  appendC0_ker D Sc cutoff i v t

theorem c0ConsumerAugmentedInverse (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    ((appendC0Splitting D Sc cutoff i v t) z).1.1 =
      z - appendOutputEmbedding D Sc cutoff i v t (appendC0 D Sc cutoff i v t z) := rfl

theorem c0ConsumerReconstruction (i : I) (v t : List I)
    (c : appendCrossingSpan D Sc cutoff i v t) (f : ℕ →₀ Old D Sc cutoff v t) :
    (appendC0Splitting D Sc cutoff i v t).symm (c, f) =
      c.1 + appendOutputEmbedding D Sc cutoff i v t f :=
  appendC0Splitting_symm D Sc cutoff i v t c f

theorem c0ConsumerDegreeZero (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    appendC0Defect D Sc cutoff i v t z = Finsupp.single 0 (appendC0Defect D Sc cutoff i v t z 0) :=
  appendC0Defect_degreeZero D Sc cutoff i v t z

theorem c0ConsumerOddSign (i : I) (hi : D.parity i = 1) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendC0 D Sc cutoff i v t
      (appendOutputDot D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g)) =
      Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ (r ≫ twist k 1 g)) :=
  appendC0_outputDot_crossing_odd D Sc cutoff i hi v s t r g

theorem c0ConsumerGlobalDot (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    appendC0 D Sc cutoff i v t (appendOutputDot D Sc cutoff i v t z) =
      appendOutputShift D Sc cutoff v t (appendC0 D Sc cutoff i v t z) +
        Finsupp.single 0 (appendC0Defect D Sc cutoff i v t z 0) :=
  appendC0_outputDot D Sc cutoff i v t z

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
