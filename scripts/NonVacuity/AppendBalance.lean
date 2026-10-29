import OddMath.QuiverHecke.CyclotomicAction.AppendBalance
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.AppendBalance then
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
namespace AppendBalanceConsumer

def poly (m : ℕ) (_ : Bool) : _root_.Polynomial ℚ :=
  _root_.Polynomial.X ^ (m + 2) + _root_.Polynomial.X ^ m

private theorem poly_parity (m : ℕ) : CyclotomicPolynomialParity datum (poly m) := by
  intro i j hj
  have hd : (poly m i).natDegree = m + 2 := by
    unfold poly
    rw [_root_.Polynomial.natDegree_add_eq_left_of_natDegree_lt] <;> simp
  rw [hd]
  have : j = m + 2 ∨ j = m := by
    by_contra h
    push_neg at h
    simp [poly, _root_.Polynomial.coeff_X_pow, h.1, h.2] at hj
  rcases this with rfl | rfl
  · rfl
  · change m • (1 : ZMod 2) = (m + 2) • (1 : ZMod 2)
    rw [add_nsmul, show (2 • (1 : ZMod 2)) = 0 by decide, add_zero]

/-- The balance of `P` for an arbitrary morphism between arbitrary words, with a cyclotomic
polynomial with two terms and an odd moving colour. -/
example (m : ℕ) (s t : List Bool)
    (g : (pres datum scalars).obj (ob datum s) ⟶ (pres datum scalars).obj (ob datum t)) :
    appendError datum scalars (poly m) true s t g ∈
      appendKill datum scalars (poly m) true s t :=
  appendError_mem_appendKill datum scalars (poly_parity m) g

end AppendBalanceConsumer
