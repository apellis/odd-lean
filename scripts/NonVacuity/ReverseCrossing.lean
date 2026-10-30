import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerMeet
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerNaturality

noncomputable section
namespace ReverseCrossingConsumer
open CategoryTheory OddMath OddMath.QuiverHecke
variable {I X k : Type*} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- Arbitrary data, including both moving-colour coincidences. -/
example (l v : List I) (i j : I) :
    reverseMeetLeft D Sc l v i j i = reverseMeetRight D Sc l v i j i :=
  reverseMeetLeft_eq_all D Sc l v i j i

example (l v : List I) (i j : I) :
    reverseMeetLeft D Sc l v i i j = reverseMeetRight D Sc l v i i j :=
  reverseMeetLeft_eq_all D Sc l v i i j

/-- Odd all-equal data use the actual normalized odd variants. -/
example (l v : List I) (i : I) (hi : D.parity i = 1) :
    crossE D Sc (l ++ [i, i, i] ++ v) l.length ≫
      OddNilHecke.Intertwiner.element (A := End ((pres D Sc).obj (ob D (l ++ [i, i, i] ++ v))))
        (dotE D Sc (l ++ [i, i, i] ++ v) (l.length + 1))
        (dotE D Sc (l ++ [i, i, i] ++ v) (l.length + 2))
        (crossE D Sc (l ++ [i, i, i] ++ v) (l.length + 1)) ≫
      sameIntertwiner D Sc (l ++ [i, i, i] ++ v) l.length i =
    OddNilHecke.Intertwiner.element (A := End ((pres D Sc).obj (ob D (l ++ [i, i, i] ++ v))))
        (dotE D Sc (l ++ [i, i, i] ++ v) (l.length + 1))
        (dotE D Sc (l ++ [i, i, i] ++ v) (l.length + 2))
        (crossE D Sc (l ++ [i, i, i] ++ v) (l.length + 1)) ≫
      sameIntertwiner D Sc (l ++ [i, i, i] ++ v) l.length i ≫
      crossE D Sc (l ++ [i, i, i] ++ v) (l.length + 1) := by
  simpa only [sameIntertwiner, hi, ite_true, Nat.add_assoc] using
    cross_comp_sameIntertwiner_sameIntertwiner D Sc l v i

/-- The unrestricted pair result is a statement about the defined reverse chain. -/
example (l : List I) (i j c : I) :
    cl D Sc (l ++ [j, c] ++ [i]) (l ++ [c, j] ++ [i]) [.cross l.length]
      (sChain_crossAt l [i] j c) ≫ reverseMoveHom D Sc i l [c, j] =
    reverseMoveHom D Sc i l [j, c] ≫
      cl D Sc (l ++ i :: [j, c]) (l ++ i :: [c, j]) [.cross (l.length + 1)]
        (sChain_cross_succ l [] i j c) :=
  cross_comp_reverseMoveHom_pair_all D Sc l i j c

#print axioms reverseMeetLeft_eq_all
#print axioms cross_comp_reverseMoveHom_pair_all
end ReverseCrossingConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[
    `OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerEqual,
    `OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerMeet]
  for owner in owners do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Module was not imported: {owner}"
    let mut count : Nat := 0
    for name in env.header.moduleData[idx]!.constNames do
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      count := count + 1
    if count == 0 then throwError "Empty declaration inventory: {owner}"
    logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
