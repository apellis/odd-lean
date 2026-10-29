import OddMath.QuiverHecke.CyclotomicAction.AppendContentCrossingImage
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.AppendContentCrossingImage then
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
namespace AppendContentCrossingImageConsumer

def poly (cutoff : ℕ) (_ : Bool) : Polynomial ℚ := Polynomial.X ^ cutoff

private theorem poly_parity (m : ℕ) : CyclotomicPolynomialParity datum (poly m) := by
  intro i j hj
  have h : j = m := by simpa [poly] using hj
  subst j
  simp [poly]

/-- Both colours, positive old height, and every cutoff including zero. -/
example (cutoff n : ℕ) (β : Multiset Bool) (i : Bool)
    (f : (Fin (n + 1) × ℕ) →₀ Hn datum scalars (n + 1))
    (b : CyclotomicContentCorner datum scalars (poly cutoff) n β) :
    appendContentCrossingTensor datum scalars (poly cutoff) n β i f b ∈
      (appendContentMackeyTarget datum scalars (poly cutoff) n β i (poly_parity cutoff)).F.range :=
  appendContentCrossingTensor_mem_range datum scalars (poly cutoff) n β i (poly_parity cutoff) f b

example (cutoff n : ℕ) (β : Multiset Bool) (i : Bool) :
    (appendContentPolynomialProjection datum scalars (poly cutoff) n β i).ker =
      (appendTargetF datum scalars i n (CyclotomicContentCorner datum scalars (poly cutoff) n β)).range :=
  appendContentPolynomialProjection_ker datum scalars (poly cutoff) n β i

example (cutoff n : ℕ) (β : Multiset Bool) (i : Bool)
    (z : appendContentSource datum scalars (poly cutoff) n β i)
    (hz : z ∈ appendContentShort datum scalars (poly cutoff) n β i) :
    ∃ f : (PrependShuffle (n + 1) × ℕ) →₀ CyclotomicContentCorner datum scalars (poly cutoff) n β,
      (∀ m, f (longPrependShuffle (n + 1), m) = 0) ∧
      appendContentP datum scalars (poly cutoff) n β i (poly_parity cutoff) z =
        f.sum (fun q b => appendContentP datum scalars (poly cutoff) n β i (poly_parity cutoff)
          (appendContentProjectCoordinates datum scalars (poly cutoff) n β i (Finsupp.single q b))) :=
  appendContentP_short_expansion datum scalars (poly cutoff) n β i (poly_parity cutoff) z hz

#print axioms OddMath.QuiverHecke.appendContentPolynomialProjection_ker
#print axioms OddMath.QuiverHecke.appendContentCrossingTensor_eq_F
#print axioms OddMath.QuiverHecke.appendContentP_project_single
#print axioms OddMath.QuiverHecke.appendContentP_short_mem_of_factorizations
end AppendContentCrossingImageConsumer
