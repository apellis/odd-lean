import OddMath.QuiverHecke.CyclotomicAction.AppendContentShortFactor
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.AppendContentShortFactor then
      for n in env.header.moduleData[i]!.constNames do
        for a in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Disallowed {a} in {n}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} declarations"

noncomputable section
open OddMath OddMath.QuiverHecke Categorification.TypeA Equiv StringDiagrams
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
namespace AppendContentShortFactorConsumer

def identityShuffle (n : ℕ) : PrependShuffle (n + 1) := ⟨1, isShuffle_one _⟩

theorem identity_short (n : ℕ) : identityShuffle n ≠ longPrependShuffle (n + 1) := by
  intro h
  have he := congrArg (fun u : PrependShuffle (n + 1) => (u.1 (Fin.last (n + 1))).val) h
  change n + 1 = (finRotate (n + 1 + 1) (Fin.last (n + 1))).val at he
  rw [finRotate_last] at he
  simp at he

/-- Both colours, arbitrary dot degree and every positive old height. -/
theorem identityEntry (n m : ℕ) (i : Bool) (s : Word Bool n) :
    appendShortEntry datum scalars (fun _ => Polynomial.X) i (identityShuffle n) m s =
      appendAlgebra datum scalars i (n + 1)
        (FiniteHomMatrix.single (prependShortOldTarget i (identityShuffle n) s) (appendWord i s)
          (appendShortOldWordHom datum scalars (fun _ => Polynomial.X) i (identityShuffle n) m s)) *
        affineLastCrossing datum scalars i i n :=
  appendShortEntry_factor datum scalars (fun _ => Polynomial.X) i
    (identityShuffle n) (identity_short n) m s

/-- Old height one and dot cutoff zero are both retained. -/
example (i : Bool) :
    appendShortEntry datum scalars (fun _ => Polynomial.X) i (identityShuffle 0) 0 ⟨[], rfl⟩ =
      appendAlgebra datum scalars i 1
        (FiniteHomMatrix.single (prependShortOldTarget i (identityShuffle 0) ⟨[], rfl⟩)
          (appendWord i ⟨[], rfl⟩)
          (appendShortOldWordHom datum scalars (fun _ => Polynomial.X) i
            (identityShuffle 0) 0 ⟨[], rfl⟩)) * affineLastCrossing datum scalars i i 0 :=
  identityEntry 0 0 i ⟨[], rfl⟩

#print axioms OddMath.QuiverHecke.appendDottedMove_short_factor
#print axioms OddMath.QuiverHecke.appendShortEntry_factor
end AppendContentShortFactorConsumer
