import OddMath.QuiverHecke.CyclotomicAction.ELVOutputOldTransport
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
example (i : I) (v t w : List I) (g : hom D Sc cutoff t w)
    (z : Target D Sc cutoff i v (t ++ [i]))
    (hz : z ∈ chronologicalShortSpan D Sc cutoff i v t) :
    act D Sc cutoff i (appendInsert D Sc cutoff i t w g) z ∈
      chronologicalShortSpan D Sc cutoff i v w :=
  act_appendInsert_chronologicalShortSpan D Sc cutoff i v t w g
    (Submodule.mem_map_of_mem hz)
example (p : ZMod 2) (i : I) (v : List I) (g : hom D Sc cutoff v v)
    (x y : Target D Sc cutoff i v (v ++ [i]))
    (h : outputLongExtraction D Sc cutoff p i v x = outputLongExtraction D Sc cutoff p i v y) :
    outputLongExtraction D Sc cutoff p i v
      (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) x) =
    outputLongExtraction D Sc cutoff p i v
      (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) y) :=
  outputLongExtraction_act_appendInsert_congr D Sc cutoff p i v g h

open scoped TensorProduct
example (i a b : I) (l r : List I)
    (c : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (h : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r))
        (cw (leadingMoveWord [] (l ++ a :: b :: r)) ++ [.cross l.length]))
      ((l ++ b :: a :: r) ++ [i]))
    (h' : SChain (i :: (l ++ a :: b :: r))
      (pl (i :: (l ++ a :: b :: r))
        ([.cross (l.length+1)] ++ cw (leadingMoveWord [] (l ++ b :: a :: r))))
      ((l ++ b :: a :: r) ++ [i])) :
    projection D Sc cutoff i (l ++ a :: b :: r) ((l ++ b :: a :: r) ++ [i])
      (c ⊗ₜ[k] (cl D Sc _ _
        (cw (leadingMoveWord [] (l ++ a :: b :: r)) ++ [.cross l.length]) h -
        SKM.zsign k (D.parity i * wordSumParity D (l ++ a :: b :: r) *
          D.parity a * D.parity b) •
        cl D Sc _ _
          ([.cross (l.length+1)] ++ cw (leadingMoveWord [] (l ++ b :: a :: r))) h')) ∈
      chronologicalShortSpan D Sc cutoff i (l ++ a :: b :: r) (l ++ b :: a :: r) :=
  bareLong_cross_chronologicalShort D Sc cutoff i a b l r c h h'

example (i a : I) (l r : List I)
    (c : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (h : SChain (i :: (l ++ a :: r))
      (pl (i :: (l ++ a :: r))
        (cw (leadingMoveWord [] (l ++ a :: r)) ++ [.dot l.length]))
      ((l ++ a :: r) ++ [i]))
    (h' : SChain (i :: (l ++ a :: r))
      (pl (i :: (l ++ a :: r))
        ([.dot (l.length+1)] ++ cw (leadingMoveWord [] (l ++ a :: r))))
      ((l ++ a :: r) ++ [i])) :
    projection D Sc cutoff i (l ++ a :: r) ((l ++ a :: r) ++ [i])
      (c ⊗ₜ[k] (cl D Sc _ _
        (cw (leadingMoveWord [] (l ++ a :: r)) ++ [.dot l.length]) h -
        SKM.zsign k (D.parity i * wordSumParity D (l ++ a :: r) * D.parity a) •
        cl D Sc _ _ ([.dot (l.length+1)] ++ cw (leadingMoveWord [] (l ++ a :: r))) h')) ∈
      chronologicalShortSpan D Sc cutoff i (l ++ a :: r) (l ++ a :: r) :=
  bareLong_dot_chronologicalShort D Sc cutoff i a l r c h h'

example (i : I) {v w : List I}
    (g : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    OutputOldComposite.error D Sc i v w g ∈
      SmallerTailNormalization.shortSpan D Sc i v (w ++ [i]) :=
  OutputOldComposite.error_mem D Sc i g

example (i : I) {v w : List I} (g : hom D Sc cutoff v w) :
    projection D Sc cutoff i v (w ++ [i])
      (bareUFull D Sc cutoff i v ≫ appendInsert D Sc cutoff i v w g -
        insert D Sc cutoff i v w (twist k (D.parity i * wordSumParity D v) g) ≫
          bareUFull D Sc cutoff i w) ∈ chronologicalShortSpan D Sc cutoff i v w :=
  bareUFull_transport D Sc cutoff i g

example (i : I) {v w : List I}
    (g h : hom D Sc cutoff v w)
    (he : (ideal D Sc cutoff v w).mkQ g = (ideal D Sc cutoff v w).mkQ h) :
    (chronologicalShortSpan D Sc cutoff i v w).mkQ
      (projection D Sc cutoff i v (w ++ [i])
        (bareUFull D Sc cutoff i v ≫ appendInsert D Sc cutoff i v w g)) =
    (chronologicalShortSpan D Sc cutoff i v w).mkQ
      (projection D Sc cutoff i v (w ++ [i])
        (bareUFull D Sc cutoff i v ≫ appendInsert D Sc cutoff i v w h)) :=
  bareUFull_old_representative_independent D Sc cutoff i g h he

open Lean in
run_cmd do
  let env ← Lean.getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVOutputOldTransport] do
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
