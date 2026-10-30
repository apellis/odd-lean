import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryInputDefect
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
      (appendOutputEmbedding D Sc cutoff i v t f) =
    appendOutputEmbedding D Sc cutoff i v t (appendInputShift D Sc cutoff i v t f) :=
  appendMovingPowerTarget_embedding_one D Sc cutoff i v t f

example (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendMovingPowerTarget D Sc cutoff i v (t ++ [i]) 1
      (appendCrossingClass D Sc cutoff i v s t r g) =
    SKM.zsign k (D.parity i * D.parity i) •
      appendCrossingClass D Sc cutoff i v s t (twist k (D.parity i) r)
        (appendMovingPower D Sc cutoff i s 1 ≫ g) -
    SKM.zsign k (D.parity i * D.parity i) •
      appendOutputEmbedding D Sc cutoff i v t
        (Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ (twist k (D.parity i) r ≫ g))) :=
  appendMovingPowerTarget_crossing_one D Sc cutoff i v s t r g

example (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    appendC0InputDefect D Sc cutoff i v t z =
      Finsupp.single 0 (appendC0InputDefect D Sc cutoff i v t z 0) :=
  appendC0InputDefect_degreeZero D Sc cutoff i v t z

example (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) :
    outputPolynomialBoundary D Sc cutoff p j v (outputCoefficientRho D Sc cutoff p j v f) =
      appendInputShift D Sc cutoff j.1 v v (outputPolynomialBoundary D Sc cutoff p j v f) +
      Finsupp.single 0
        (appendC0InputDefect D Sc cutoff j.1 v v (outputLiftBoundary D Sc cutoff p j v f) 0) :=
  outputPolynomialBoundary_rho D Sc cutoff p j v f

run_cmd do
  let env ← Lean.getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryInputDefect
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
