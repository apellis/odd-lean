import OddMath.QuiverHecke.CyclotomicAction.ELVQPNumerator
noncomputable section
open CategoryTheory Polynomial OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v : List I) :
    (normalizedEndpointQPPolynomial D Sc cutoff i v).Monic :=
  normalizedEndpointQPPolynomial_monic D Sc cutoff i v

example (i : I) (v : List I) :
    (normalizedEndpointQPPolynomial D Sc cutoff i v).eval₂ (RingHom.id _)
      (affineUnitEndHom D Sc cutoff (v ++ [i]) (dotE D Sc (v ++ [i]) v.length)) =
      normalizedEndpointQPNumerator D Sc cutoff i v :=
  normalizedEndpointQPPolynomial_eval D Sc cutoff i v

example (i : I) (v w : List I) (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (normalizedEndpointQPNumerator D Sc cutoff i v ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 :=
  normalizedEndpointQPNumerator_regular D Sc cutoff i v w h hh

example (i : I) (v : List I) (p : Polynomial (End (obj D Sc cutoff (v ++ [i])))) :
    p %ₘ normalizedEndpointQPPolynomial D Sc cutoff i v = 0 ∨
      (p %ₘ normalizedEndpointQPPolynomial D Sc cutoff i v).degree <
        (normalizedEndpointQPPolynomial D Sc cutoff i v).degree :=
  normalizedEndpointQPPolynomial_remainder_bound D Sc cutoff i v p

#print axioms normalizedEndpointQPPolynomial_monic
#print axioms normalizedEndpointQPPolynomial_eval
#print axioms normalizedEndpointQPNumerator_regular
#print axioms normalizedEndpointQPPolynomial_rightDivision
#print axioms normalizedEndpointQPPolynomial_remainder_bound
#print axioms normalizedEndpointQPPolynomial_eval_right_power

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVQPNumerator,
      `OddMath.QuiverHecke.CyclotomicAction.EndpointNormPolynomial,
      `OddMath.QuiverHecke.CyclotomicAction.EndpointNormEvaluation,
      `OddMath.QuiverHecke.CyclotomicAction.ELVMonicPolynomial] do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Module was not imported: {owner}"
    let mut count : Nat := 0
    for name in env.header.moduleData[idx]!.constNames do
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      count := count + 1
    if count == 0 then throwError "Empty declaration inventory: {owner}"
    logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."
