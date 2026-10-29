import OddMath.QuiverHecke.CyclotomicAction.PrependTwistCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.PrependTwistCoordinates then
      for n in env.header.moduleData[i]!.constNames do
        for a in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Disallowed {a} in {n}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} declarations"

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
namespace PrependTwistCoordinatesConsumer

/-- The twisted prepend coordinates over the asymmetric parameter datum, for every parity. -/
example (n : ℕ) (ε : ZMod 2) (q : PrependShuffle (n + 1) × ℕ) (m : PUnit) :
    prependTwistCoordinates datum scalars true n ε PUnit (Finsupp.single q m) =
      Categorification.InductionAlong.Ind.tmul
        ((prependTwistCorner datum scalars true n ε).symm
          (prependPBWCorner datum scalars true q.1 q.2 1)) m :=
  prependTwistCoordinates_single datum scalars true n ε PUnit q m

end PrependTwistCoordinatesConsumer
