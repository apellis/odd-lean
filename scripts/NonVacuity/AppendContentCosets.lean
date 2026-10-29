import OddMath.QuiverHecke.CyclotomicAction.AppendContentCosets
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.AppendContentCosets then
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
namespace AppendContentCosetsConsumer

def poly (cutoff : ℕ) (_ : Bool) : Polynomial ℚ := Polynomial.X ^ cutoff

/-- Both colours, both cutoff parities and cutoff zero use the same content-corner maps. -/
example (cutoff n : ℕ) (β : Multiset Bool) (i : Bool)
    (f : ℕ →₀ CyclotomicContentCorner datum scalars (poly cutoff) n β) :
    appendContentLongExtract datum scalars (poly cutoff) n β i
      (appendContentLongLift datum scalars (poly cutoff) n β i f) = f :=
  appendContentLongExtract_lift datum scalars (poly cutoff) n β i f

/-- The prescribed two-term lifts are independent modulo the short subgroup. -/
example (cutoff : ℕ) (β : Multiset Bool) (i : Bool)
    (b c : CyclotomicContentCorner datum scalars (poly cutoff) 0 β) :
    appendContentLongLift datum scalars (poly cutoff) 0 β i
      (Finsupp.single 0 b + Finsupp.single 1 c) ∈
        appendContentShort datum scalars (poly cutoff) 0 β i ↔ b = 0 ∧ c = 0 := by
  rw [appendContentLongLift_short_iff]
  constructor
  · intro h
    have h₀ := congrArg (fun f => f 0) h
    have h₁ := congrArg (fun f => f 1) h
    simpa using And.intro h₀ h₁
  · rintro ⟨rfl, rfl⟩
    simp

/-- Covering is in the existing left append-idempotent source, not a replacement group. -/
example (cutoff n : ℕ) (β : Multiset Bool) (i : Bool)
    (z : appendContentSource datum scalars (poly cutoff) n β i) :
    z - appendContentLongLift datum scalars (poly cutoff) n β i
      (appendContentLongExtract datum scalars (poly cutoff) n β i z) ∈
        appendContentShort datum scalars (poly cutoff) n β i :=
  appendContentLong_cover datum scalars (poly cutoff) n β i z

example (cutoff n : ℕ) (β : Multiset Bool) (i : Bool)
    (b : CyclotomicContentCorner datum scalars (poly cutoff) n β)
    (f : ℕ →₀ CyclotomicContentCorner datum scalars (poly cutoff) n β) :
    appendContentLongLift datum scalars (poly cutoff) n β i
      (CyclotomicAction.BoundaryPolynomial.rsmul b f) =
        appendContentSourceRightMul datum scalars (poly cutoff) n β i b
          (appendContentLongLift datum scalars (poly cutoff) n β i f) :=
  appendContentLongLift_rightMul datum scalars (poly cutoff) n β i b f

/-- The affine corner calculation also includes genuinely zero old height. -/
example (i : Bool) (s : Word Bool 0) :
    prependShuffleTarget i (longPrependShuffle 0) s = appendWord i s :=
  prependShuffleTarget_long i s

#print axioms OddMath.QuiverHecke.appendContentLongExtract_lift
#print axioms OddMath.QuiverHecke.appendContentShort_iff_expansion
#print axioms OddMath.QuiverHecke.appendContentLongLift_rightMul
end AppendContentCosetsConsumer
