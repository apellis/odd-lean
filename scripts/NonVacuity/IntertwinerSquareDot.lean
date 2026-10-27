import OddMath.QuiverHecke.CyclotomicAction.IntertwinerSquareDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.IntertwinerSquareDot then
      for n in env.header.moduleData[i]!.constNames do
        for a in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Disallowed {a} in {n}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} declarations"

noncomputable section
open StringDiagrams OddMath.QuiverHecke Categorification
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
namespace IntertwinerSquareDotConsumer

def polys (_ : Bool) : _root_.Polynomial ℚ := _root_.Polynomial.X ^ 3

private theorem polys_parity : CyclotomicPolynomialParity datum polys := by
  intro i m hm
  by_cases h : 3 = m
  · subst m; simp [polys]
  · simp [polys, Polynomial.coeff_X_pow, Ne.symm h] at hm

example (r : Hn datum scalars 0) := affineFirstDot_sq_comm datum scalars true 0 r

example (n : ℕ) (r : Hn datum scalars n) := affineFirstDot_sq_comm datum scalars true n r

example (n : ℕ) (β : Multiset Bool)
    (x : InductionAlong.Corner (prependAlgebra datum scalars true (n + 1) :
      Hn datum scalars (n + 1) →ₙ+* Hn datum scalars (n + 1 + 1)))
    (b : (qCoefficient datum scalars true β polys polys_parity n).toSVec) :
    (targetRightDot datum scalars true β polys polys_parity n ^ 2)
        (InductionAlong.Ind.tmul x b) =
      InductionAlong.Ind.tmul
        (targetDotCorner datum scalars true (n + 1)
          (targetDotCorner datum scalars true (n + 1) x)) b :=
  targetRightDot_sq_tmul datum scalars true β polys polys_parity n x b

example (n : ℕ) (β : Multiset Bool)
    (x : InductionAlong.Corner (qPrependAlgebra datum scalars true β n))
    (b : qContentCoefficient datum scalars true β polys polys_parity n) :=
  contentTargetRightDot_sq_tmul datum scalars true β polys polys_parity n x b

end IntertwinerSquareDotConsumer
