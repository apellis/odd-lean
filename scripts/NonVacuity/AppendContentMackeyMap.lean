import OddMath.QuiverHecke.CyclotomicAction.AppendContentMackeyMap
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.AppendContentMackeyMap then
      for n in env.header.moduleData[i]!.constNames do
        for a in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Disallowed {a} in {n}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} declarations"

noncomputable section
open OddMath.QuiverHecke
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
namespace AppendContentMackeyMapConsumer

def poly (m : ℕ) (_ : Bool) : Polynomial ℚ := Polynomial.X ^ m

private theorem poly_parity (m : ℕ) : CyclotomicPolynomialParity datum (poly m) := by
  intro i j hj
  have h : j = m := by simpa [poly] using hj
  subst j
  simp [poly]

/-- Actual cyclotomic content corners, including zero cutoff and both cutoff parities. -/
example (m n : ℕ) (β : Multiset Bool) (i : Bool)
    (b : CyclotomicContentCorner datum scalars (poly m) n β)
    (z : appendContentSource datum scalars (poly m) n β i) :
    appendContentP datum scalars (poly m) n β i (poly_parity m)
        (appendContentSourceRightMul datum scalars (poly m) n β i b z) =
      appendTensorRightMul datum scalars i n _ b
        (appendContentP datum scalars (poly m) n β i (poly_parity m) z) :=
  appendContentP_rightMul datum scalars (poly m) n β i (poly_parity m) b z

/-- The exact signed dot equation on the same content-corner source and target. -/
example (m n : ℕ) (β : Multiset Bool) (i : Bool)
    (z : appendContentSource datum scalars (poly m) n β i) :
    appendContentP datum scalars (poly m) n β i (poly_parity m)
        (appendContentRho datum scalars (poly m) n β i (poly_parity m) z) =
      (appendContentMackeyTarget datum scalars (poly m) n β i (poly_parity m)).Rt
        (appendContentP datum scalars (poly m) n β i (poly_parity m) z) :=
  appendContentP_rho datum scalars (poly m) n β i (poly_parity m) z

#print axioms OddMath.QuiverHecke.appendContentP_rightMul
#print axioms OddMath.QuiverHecke.appendContentP_rho
end AppendContentMackeyMapConsumer
