import OddMath.QuiverHecke.CyclotomicAction.AppendContentRhoCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.AppendContentRhoCoordinates then
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
namespace AppendContentRhoCoordinatesConsumer

def poly (cutoff : ℕ) (_ : Bool) : Polynomial ℚ := Polynomial.X ^ cutoff

private theorem poly_parity (m : ℕ) : CyclotomicPolynomialParity datum (poly m) := by
  intro i j hj
  have h : j = m := by simpa [poly] using hj
  subst j
  simp [poly]

/-- Both colours and every cutoff, including zero, use the normalized section. -/
example (cutoff n : ℕ) (β : Multiset Bool) (i : Bool)
    (f : ℕ →₀ CyclotomicContentCorner datum scalars (poly cutoff) n β) :
    appendContentRhoExtract datum scalars (poly cutoff) n β i
      (appendContentRhoLift datum scalars (poly cutoff) n β i f) = f :=
  appendContentRhoExtract_lift datum scalars (poly cutoff) n β i f

example (cutoff n : ℕ) (β : Multiset Bool) (i : Bool)
    (f : ℕ →₀ CyclotomicContentCorner datum scalars (poly cutoff) n β) :
    appendContentRho datum scalars (poly cutoff) n β i (poly_parity cutoff)
      (appendContentRhoLift datum scalars (poly cutoff) n β i f) =
      appendContentRhoLift datum scalars (poly cutoff) n β i
        (movingParityRaise
          (contentCornerParity datum scalars (poly cutoff) n β i (poly_parity cutoff)).toAddMonoidHom f) :=
  appendContentRho_lift datum scalars (poly cutoff) n β i (poly_parity cutoff) f

/-- Extraction compatibility is tested on the entire source, not only its long lifts. -/
example (cutoff n : ℕ) (β : Multiset Bool) (i : Bool)
    (z : appendContentSource datum scalars (poly cutoff) n β i) :
    appendContentRhoExtract datum scalars (poly cutoff) n β i
      (appendContentRho datum scalars (poly cutoff) n β i (poly_parity cutoff) z) =
      movingParityRaise
        (contentCornerParity datum scalars (poly cutoff) n β i (poly_parity cutoff)).toAddMonoidHom
        (appendContentRhoExtract datum scalars (poly cutoff) n β i z) :=
  appendContentRhoExtract_rho datum scalars (poly cutoff) n β i (poly_parity cutoff) z

example (cutoff n : ℕ) (β : Multiset Bool) (i : Bool)
    (z : appendContentSource datum scalars (poly cutoff) n β i)
    (hz : z ∈ appendContentShort datum scalars (poly cutoff) n β i) :
    appendContentRho datum scalars (poly cutoff) n β i (poly_parity cutoff) z ∈
      appendContentShort datum scalars (poly cutoff) n β i :=
  appendContentShort_rho datum scalars (poly cutoff) n β i (poly_parity cutoff) z hz

/-- The affine unit-coefficient calculation covers genuinely zero old height.
The content-corner recurrence above instead starts at old height one. -/
example (i : Bool) (m : ℕ) :
    prependPBWTerm datum scalars i (longPrependShuffle 0) m 1 *
        affineFirstDot datum scalars i 0 =
      prependPBWTerm datum scalars i (longPrependShuffle 0) (m + 1) 1 :=
  prependPBWTerm_one_mul_firstDot datum scalars i (longPrependShuffle 0) m

#print axioms OddMath.QuiverHecke.appendContentRho_lift
#print axioms OddMath.QuiverHecke.appendContentRhoExtract_rho
#print axioms OddMath.QuiverHecke.appendContentP_rhoLift
end AppendContentRhoCoordinatesConsumer
