import OddMath.QuiverHecke.CyclotomicAction.ELVOutputOrderBalance
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
example (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) (n : ℕ) (g : hom D Sc cutoff v v) :
    outputLongCoordinate D Sc cutoff p i v n
      (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) z) =
    oldComp D Sc cutoff v v v (outputLongCoordinate D Sc cutoff p i v n z)
      (oldTwist D Sc cutoff (p + ((n : ZMod 2) * D.parity i + D.parity i * wordSumParity D v)) v v
        ((ideal D Sc cutoff v v).mkQ g)) :=
  outputLongCoordinate_outputOld D Sc cutoff p i v z n g

example (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) (n : ℕ) (c : Old D Sc cutoff v v) :
    outputOldExtraction D Sc cutoff p i v z c n =
      oldComp D Sc cutoff v v v (outputLongCoordinate D Sc cutoff p i v n z)
        (oldTwist D Sc cutoff
          (p + D.parity i * wordSumParity D v + (n : ZMod 2) * D.parity i) v v c) :=
  outputOldExtraction_coordinate D Sc cutoff p i v z n c

example (p : ZMod 2) (i : I) (v : List I) (n : ℕ)
    (h : hom D Sc cutoff (i :: v) (v ++ [i])) (b c : Old D Sc cutoff v v) :
    outputOldExtraction D Sc cutoff p i v
      (balancedForward D Sc cutoff p i v (v ++ [i]) (balancedTmul D Sc cutoff p i h b)) c n =
    oldComp D Sc cutoff v v v
      (oldComp D Sc cutoff v v v b
        (outputLongCoordinate D Sc cutoff p i v n (projection D Sc cutoff i v (v ++ [i]) h)))
      (oldTwist D Sc cutoff
        (p + D.parity i * wordSumParity D v + (n : ZMod 2) * D.parity i) v v c) :=
  outputLongCoordinate_twoSided_balanced D Sc cutoff p i v n h b c

example (p : ZMod 2) (i : I) (v : List I) (m n : ℕ)
    (b c : Old D Sc cutoff v v) (g : hom D Sc cutoff v v)
    (hg : (ideal D Sc cutoff v v).mkQ g = c) :
    outputLongCoordinate D Sc cutoff p i v n
      (balancedForward D Sc cutoff p i v (v ++ [i])
        (balancedTmul D Sc cutoff p i
          ((bareUFull D Sc cutoff i v ≫ appendInsert D Sc cutoff i v v g) ≫
            appendMovingPower D Sc cutoff i v m) b)) =
      if n = m then oldComp D Sc cutoff v v v b
        (oldTwist D Sc cutoff (p + D.parity i * wordSumParity D v) v v c) else 0 :=
  canonical_output_balanced D Sc cutoff p i v m n b c g hg

example (p : ZMod 2) (i : I) (v : List I) (m : ℕ)
    (b c : Old D Sc cutoff v v) (g : hom D Sc cutoff v v)
    (hg : (ideal D Sc cutoff v v).mkQ g = c) :
    outputLongExtraction D Sc cutoff p i v
      (pair D Sc cutoff p i
        ((bareUFull D Sc cutoff i v ≫ appendInsert D Sc cutoff i v v g) ≫
          appendMovingPower D Sc cutoff i v m) b) =
      Finsupp.single m (oldComp D Sc cutoff v v v b
        (oldTwist D Sc cutoff (p + D.parity i * wordSumParity D v) v v c)) :=
  canonical_output_extraction D Sc cutoff p i v m b c g hg

open Lean in
run_cmd do
  let env ← Lean.getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVOutputOldTransport,
      `OddMath.QuiverHecke.CyclotomicAction.ELVOutputOrderBalance] do
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
