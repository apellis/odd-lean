import OddMath.QuiverHecke.CyclotomicAction.AppendContentShortImage
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if moduleNames[idx.toNat]! ==
          `OddMath.QuiverHecke.CyclotomicAction.AppendContentShortImage then
        for a in (← Lean.collectAxioms name) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Disallowed {a} in {name}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} owned declarations"

noncomputable section
open OddMath.QuiverHecke Categorification.TypeA Equiv
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
namespace AppendContentShortImageConsumer

def poly (cutoff : ℕ) (_ : Bool) : Polynomial ℚ := Polynomial.X ^ cutoff

private theorem poly_parity (m : ℕ) : CyclotomicPolynomialParity datum (poly m) := by
  intro i j hj
  have h : j = m := by simpa [poly] using hj
  subst j
  simp [poly]

def identityShuffle (n : ℕ) : PrependShuffle (n + 1) := ⟨1, isShuffle_one _⟩

theorem identity_short (n : ℕ) : identityShuffle n ≠ longPrependShuffle (n + 1) := by
  intro h
  have he := congrArg (fun u : PrependShuffle (n + 1) => (u.1 (Fin.last (n + 1))).val) h
  change n + 1 = (finRotate (n + 1 + 1) (Fin.last (n + 1))).val at he
  rw [finRotate_last] at he
  simp at he

/-- Both colours and all dot degrees, including old height one and cutoff zero. -/
example (cutoff n m : ℕ) (i : Bool) :
    ∃ f : (Fin (n + 1) × ℕ) →₀ Hn datum scalars (n + 1),
      appendAlgebra datum scalars i (n + 1) 1 *
        (prependPBWTerm datum scalars i (identityShuffle n) m 1 *
          appendMoveMatrix datum scalars (poly cutoff) i n) =
        appendLeftSum datum scalars i n f :=
  projected_short_multiplier_factor datum scalars (poly cutoff) i n
    (identityShuffle n) (identity_short n) m

/-- Every element of the concrete short submodule, with no factorization hypothesis. -/
example (cutoff n : ℕ) (β : Multiset Bool) (i : Bool)
    (z : appendContentShort datum scalars (poly cutoff) n β i) :
    appendContentP datum scalars (poly cutoff) n β i (poly_parity cutoff) z.1 ∈
      (appendContentMackeyTarget datum scalars (poly cutoff) n β i (poly_parity cutoff)).F.range :=
  appendContentP_short_mem datum scalars (poly cutoff) n β i (poly_parity cutoff) z.1 z.2

#print axioms OddMath.QuiverHecke.projected_short_multiplier_sum
#print axioms OddMath.QuiverHecke.projected_short_multiplier_factor
#print axioms OddMath.QuiverHecke.appendContentP_short_mem
end AppendContentShortImageConsumer
