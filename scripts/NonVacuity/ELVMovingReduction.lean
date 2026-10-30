import OddMath.QuiverHecke.CyclotomicAction.ELVMovingReduction
noncomputable section
open CategoryTheory Polynomial OddMath OddMath.QuiverHecke ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

example (i : I) (v : List I) :
    (monicELVEndpointProduct D Sc cutoff i v).Monic :=
  monicELVEndpointProduct_monic D Sc cutoff i v

example (i : I) (v : List I) :
    (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
      (monicELVEndpointValue D Sc cutoff i v) = 0 :=
  monicELVEndpointProduct_annihilates D Sc cutoff i v

example (i : I) (v : List I) (n : ℕ) :
    (monicELVEndpointProduct D Sc cutoff i v).coeff n ∈
      (rightContextEndHom D Sc cutoff i v).range :=
  monicELVEndpointProduct_coeff_mem_range D Sc cutoff i v n

example (i : I) (v : List I) (n : ℕ) :
    (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
      ((affineUnitEndHom D Sc cutoff (v ++ [i])
        (dotE D Sc (v ++ [i]) v.length)) ^ n) ∈
    Submodule.span k {z | ∃ a : End (obj D Sc cutoff v),
      ∃ j < (monicELVEndpointProduct D Sc cutoff i v).natDegree,
        z = (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
          (rightContextEndHom D Sc cutoff i v a *
            (affineUnitEndHom D Sc cutoff (v ++ [i])
              (dotE D Sc (v ++ [i]) v.length)) ^ j)} :=
  movingDot_pow_mem_bounded_old_span D Sc cutoff i v n

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners := #[
    `OddMath.QuiverHecke.CyclotomicAction.EndpointNormPolynomial,
    `OddMath.QuiverHecke.CyclotomicAction.EndpointNormEvaluation,
    `OddMath.QuiverHecke.CyclotomicAction.ELVMonicPolynomial,
    `OddMath.QuiverHecke.CyclotomicAction.ELVMonicAnnihilator,
    `OddMath.QuiverHecke.CyclotomicAction.ELVMonicOldCoefficients,
    `OddMath.QuiverHecke.CyclotomicAction.ELVMovingReduction]
  for owner in owners do
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
