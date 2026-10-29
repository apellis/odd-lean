import OddMath.QuiverHecke.CyclotomicAction.AppendContentBoundary
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.AppendContentBoundary then
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
namespace AppendContentBoundaryConsumer

def poly (cutoff : ℕ) (_ : Bool) : Polynomial ℚ := Polynomial.X ^ cutoff

private theorem poly_parity (m : ℕ) : CyclotomicPolynomialParity datum (poly m) := by
  intro i j hj
  have h : j = m := by simpa [poly] using hj
  subst j
  simp [poly]

/-- The constructor has the actual moving map, not a supplied abstract boundary. -/
example (cutoff n : ℕ) (β : Multiset Bool) (i : Bool) :
    (appendContentMackeyBoundary datum scalars (poly cutoff) n β i (poly_parity cutoff)).P =
      appendContentP datum scalars (poly cutoff) n β i (poly_parity cutoff) := rfl

open CyclotomicAction.BoundaryPolynomial

/-- Both parities, every cutoff (including zero), and old height one are included. -/
example (cutoff n : ℕ) (β : Multiset Bool) (i : Bool)
    (f : ℕ →₀ CyclotomicContentCorner datum scalars (poly cutoff) n β) :
    let σ := contentCornerParity datum scalars (poly cutoff) n β i (poly_parity cutoff)
    let M := appendContentMackeyBoundary datum scalars (poly cutoff) n β i (poly_parity cutoff)
    let T := appendContentMackeyTarget datum scalars (poly cutoff) n β i (poly_parity cutoff)
    M.A (tShift σ f) - tShift σ (M.A f) = Finsupp.single 0
      (T.E (appendContentBoundaryCrossing datum scalars (poly cutoff) n β i (poly_parity cutoff) f)) :=
  appendContentBoundary_defect datum scalars (poly cutoff) n β i (poly_parity cutoff) f

example (cutoff n m : ℕ) (β : Multiset Bool) (i : Bool) :
    DegLT ((appendContentMackeyBoundary datum scalars (poly cutoff) n β i
      (poly_parity cutoff)).φ (m + 1) -
      tShift (contentCornerParity datum scalars (poly cutoff) n β i (poly_parity cutoff))
        ((appendContentMackeyBoundary datum scalars (poly cutoff) n β i
          (poly_parity cutoff)).φ m)) 1 :=
  (appendContentMackeyBoundary datum scalars (poly cutoff) n β i (poly_parity cutoff)).recurrence m

/-- No monicity or nonzero-polynomial hypothesis is hidden in the constructor. -/
example (β : Multiset Bool) (i : Bool) :
    MackeyCosets (contentCornerParity datum scalars (fun _ => 0) 0 β i (by simp [CyclotomicPolynomialParity]))
      (appendContentSource datum scalars (fun _ => 0) 0 β i)
      (appendTensorFixed datum scalars i 0 (CyclotomicContentCorner datum scalars (fun _ => 0) 0 β))
      (appendTensorLeftCoordinates datum scalars i 0 (CyclotomicContentCorner datum scalars (fun _ => 0) 0 β)) :=
  appendContentMackeyCosets datum scalars (fun _ => 0) 0 β i (by simp [CyclotomicPolynomialParity])

#print axioms OddMath.QuiverHecke.appendContentMackeyCosets
#print axioms OddMath.QuiverHecke.appendContentBoundary_factor
#print axioms OddMath.QuiverHecke.appendContentBoundary_firstOrder
end AppendContentBoundaryConsumer
