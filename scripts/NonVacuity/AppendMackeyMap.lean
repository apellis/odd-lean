import OddMath.QuiverHecke.CyclotomicAction.AppendMackeyMap
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.AppendMackeyMap then
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
namespace AppendMackeyMapConsumer

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
    simp only [not_or] at h
    simp [poly, _root_.Polynomial.coeff_X_pow, h.1, h.2] at hj
  rcases this with h | h <;> rw [h]
  rw [add_nsmul, two_nsmul, CharTwo.add_self_eq_zero, add_zero]

/-- The entries of `W ψ(a)` for a single matrix entry, over the asymmetric parameter datum. -/
example (m n : ℕ) (s t : Word Bool (n + 1)) (g : wordObj datum scalars t ⟶ wordObj datum scalars s) :
    appendMoveMatrix datum scalars (poly m) true n *
        appendAlgebra datum scalars true (n + 1) (OddMath.FiniteHomMatrix.single s t g) =
      OddMath.FiniteHomMatrix.single (prependWord true s) (appendWord true t)
        (appendHom datum scalars true t s g ≫ appendW datum scalars (poly m) true s.1) :=
  appendMoveMatrix_mul_append datum scalars (poly m) true n s t g

/-- The descended append Mackey map, for every parity `ε`, with every hypothesis proved (on the
zero module). -/
example (m n : ℕ) (ε : ZMod 2) :
    Categorification.InductionAlong.Ind PUnit (prependTwist datum scalars true n ε) →ₗ[Hn datum scalars (n + 1 + 1)]
      Categorification.InductionAlong.Ind PUnit
        (appendAlgebra datum scalars true (n + 1) :
          Hn datum scalars (n + 1) →ₙ+* Hn datum scalars (n + 1 + 1)) :=
  appendMackeyMap datum scalars (N := PUnit) (poly_parity m) (fun _ _ _ => Subsingleton.elim _ _)
    (fun _ _ _ => Subsingleton.elim _ _)

end AppendMackeyMapConsumer
