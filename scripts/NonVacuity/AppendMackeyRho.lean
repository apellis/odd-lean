import OddMath.QuiverHecke.CyclotomicAction.AppendMackeyRho
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.AppendMackeyRho then
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
namespace AppendMackeyRhoConsumer

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

/-- The first-dot slide of the descended append Mackey map, with every hypothesis proved (on the
zero module). -/
example (m n : ℕ) (ε : ZMod 2)
    (t : Categorification.InductionAlong.Ind PUnit (prependTwist datum scalars true n ε)) :
    appendMackeyMap datum scalars (N := PUnit) (poly_parity m) (fun _ _ _ => Subsingleton.elim _ _)
        (fun _ _ _ => Subsingleton.elim _ _)
        (appendSourceDot datum scalars true n ε (0 : PUnit →+ PUnit)
          (fun _ _ => Subsingleton.elim _ _) t) =
      OddMath.SKM.zsign ℤ (appendSourceSign datum (poly m) true ε) •
        appendTensorRightDot datum scalars true n PUnit (0 : PUnit →+ PUnit)
          (fun _ _ => Subsingleton.elim _ _)
          (appendMackeyMap datum scalars (N := PUnit) (poly_parity m)
            (fun _ _ _ => Subsingleton.elim _ _) (fun _ _ _ => Subsingleton.elim _ _) t) :=
  appendMackeyMap_appendSourceDot datum scalars true n ε _ _ (poly_parity m) _ _ t

end AppendMackeyRhoConsumer
