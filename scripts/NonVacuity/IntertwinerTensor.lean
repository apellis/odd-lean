import OddMath.QuiverHecke.CyclotomicAction.IntertwinerTensor
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if #[`OddMath.QuiverHecke.CyclotomicAction.IntertwinerCorners,
        `OddMath.QuiverHecke.CyclotomicAction.IntertwinerTensor].contains env.header.moduleNames[i]! then
      for n in env.header.moduleData[i]!.constNames do
        for a in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Disallowed {a} in {n}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} declarations"

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke Categorification
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
namespace IntertwinerTensorConsumer

/-- The same asymmetric Cartan datum, with one even and one odd colour. -/
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

/-- An odd-height all-odd content activates the involution. -/
example (z : Hn datum scalars 3) :=
  contentMove_balance datum scalars true 3 ({false, true, false} : Multiset Bool) z

/-- Mixed parity with an odd total content also activates the twist. -/
example (z : Hn mixedDatum mixedScalars 2) :=
  contentMove_balance mixedDatum mixedScalars true 2 ({false, true} : Multiset Bool) z

/-- Pure tensors in the actual balanced quotient, with the regular coefficient module. -/
example := contentQ_tmul datum scalars true 3 ({false, true, false} : Multiset Bool)
  (Hn datum scalars 3)
  (InductionAlong.unitGen (appendAlgebra datum scalars true 3 :
    Hn datum scalars 3 →ₙ+* Hn datum scalars 4)) (1 : Hn datum scalars 3)

example := contentQ_tmul mixedDatum mixedScalars true 2 ({false, true} : Multiset Bool)
  (Hn mixedDatum mixedScalars 2)
  (InductionAlong.unitGen (appendAlgebra mixedDatum mixedScalars true 2 :
    Hn mixedDatum mixedScalars 2 →ₙ+* Hn mixedDatum mixedScalars 3))
  (1 : Hn mixedDatum mixedScalars 2)

/-- The descended map accepts the cyclotomic quotient, without a balance hypothesis. -/
example := cyclotomicContentQ datum scalars true 2 ({false, true, false} : Multiset Bool)
  (fun _ => _root_.Polynomial.X ^ 4)

example := cyclotomicContentQ mixedDatum mixedScalars true 1 ({false, true} : Multiset Bool)
  (fun _ => _root_.Polynomial.X ^ 4)

end IntertwinerTensorConsumer
