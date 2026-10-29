import OddMath.QuiverHecke.CyclotomicAction.MoveHomLeading
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.MoveHomLeading then
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
namespace MoveHomLeadingConsumer

def mixedDatum : OddMath.SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }

def mixedScalars : OddMath.SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

/-- Both moving parities and every spectator word, with no leading-term premise. -/
theorem filtered (i : Bool) (l ν : List Bool) :
    moveHom mixedDatum mixedScalars i l ν - leadingMoveHom mixedDatum mixedScalars i l ν ∈
      Low mixedDatum mixedScalars (l ++ i :: ν) (l ++ ν ++ [i]) ν.length :=
  moveHom_sub_leading_mem_low mixedDatum mixedScalars i l ν

example (l ν : List Bool) := filtered false l ν
example (l ν : List Bool) := filtered true l ν

example (i : Bool) (ν : List Bool) (x : PrependIdx i ν (ν ++ [i]))
    (hx : x.1.2.2.2 = longPrependShuffle ν.length) :
    (prependBasis mixedDatum mixedScalars).repr (moveHom mixedDatum mixedScalars i [] ν) x =
      (prependBasis mixedDatum mixedScalars).repr (leadingMoveHom mixedDatum mixedScalars i [] ν) x :=
  moveHom_long_prepend_repr mixedDatum mixedScalars i ν x hx

#print axioms OddMath.QuiverHecke.moveHom_sub_leading_mem_low
#print axioms OddMath.QuiverHecke.moveHom_long_prepend_repr
end MoveHomLeadingConsumer
