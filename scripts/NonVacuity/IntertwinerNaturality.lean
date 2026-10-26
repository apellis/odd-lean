import OddMath.QuiverHecke.CyclotomicAction.IntertwinerNaturality
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! ==
        `OddMath.QuiverHecke.CyclotomicAction.IntertwinerNaturality then
      for n in env.header.moduleData[i]!.constNames do
        for a in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Disallowed {a} in {n}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} declarations"

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters

/-- All Hom entries on a genuinely odd, mixed-colour word; no word-form or
homogeneity hypothesis on the tested morphism. -/
example (f : (pres datum scalars).obj (ob datum [false, true, false]) ⟶
    (pres datum scalars).obj (ob datum [false, true, false])) :=
  hom_comp_moveHom datum scalars true f

/-- The parity twist is active: identity plus an odd dot is inhomogeneous. -/
example := hom_comp_moveHom datum scalars true
  ((1 : End ((pres datum scalars).obj (ob datum [false, true, false]))) +
    dotE datum scalars [false, true, false] 0)

/-- The old crossing with repeated outside colour is covered as well. -/
example := hom_comp_moveHom datum scalars true
  (cl datum scalars [false, true] [true, false] [.cross 0]
    (sChain_pl [false, true] [.cross 0]))
