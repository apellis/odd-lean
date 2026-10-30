import OddMath.QuiverHecke.CyclotomicAction.ELVOutputSLeading
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v : List I) :
    (independentOutputS D Sc cutoff i v).support ⊆ Finset.range (outputSDegree D i v + 1) :=
  independentOutputS_support D Sc cutoff i v

example (i : I) (v : List I) :
    independentOutputS D Sc cutoff i v (outputSDegree D i v) =
      (ideal D Sc cutoff v v).mkQ (𝟙 _) :=
  independentOutputS_top D Sc cutoff i v

example (i : I) (v : List I) :
    independentOutputS D Sc cutoff i v (outputSDegree D i v + 1) = 0 :=
  independentOutputS_above D Sc cutoff i v _ (Nat.lt_succ_self _)

run_cmd do
  let env ← Lean.getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVOutputSLeading
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  let mut count : Nat := 0
  for name in env.header.moduleData[idx]!.constNames do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    Lean.logInfo m!"AUDIT {owner} {name}: {axioms}"
    count := count + 1
  if count == 0 then throwError "Empty declaration inventory for {owner}"
  Lean.logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
